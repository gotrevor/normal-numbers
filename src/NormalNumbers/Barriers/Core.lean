/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Lean

/-!
# Barrier library: the record type and `#barrier_audit`

A **barrier** is a known-false (or known-strange) sibling object together with the Lean
declaration that settles it: Stoneham's `α_{2,3}` is normal in base 2 and not in base 6, a
Cantor–Liouville point is never normal to a base divisible by 3, and so on.  A **crux** is a
frozen headline `sorry`.  The difficulty check says every crux names a sibling its mechanism must
fail on.  This file turns that check from prose into a build failure, as `MazeAudit.lean` did for
the Maze rows.

* `Barrier` carries the sibling's statement as a `Prop` and an `Evidence` term **of that
  statement**, so the elaborator checks that the cited theorem proves exactly what the barrier
  claims.  `decls` names the declarations; the audit checks they occur in the barrier's value.
* `Tier` is a claim the audit checks with `collectAxioms`: `proved` and `cited` barriers must be
  free of `sorryAx`; a `frozen` barrier must still contain one.  When a frozen barrier gets
  proved, the audit demands its promotion to `proved`.
* `#barrier_audit barriers, cruxes, waivers` fails the build unless every declaration in scope
  with a **direct** `sorry` is either a crux linked to at least one barrier, a waiver with a
  reason, or the declaration of a frozen barrier.  The full list of checks is on
  `auditBarriers`.  The root file `NormalNumbers.lean` runs it last, over every module.

Names are written as ``` ``Foo.bar ``` literals, so a missing or renamed declaration breaks the
build at the registry, before the audit runs.
-/

namespace NormalNumbers.Barriers

open Lean Elab Command

/-- How a barrier is settled. -/
inductive Tier where
  /-- A theorem in this build, free of `sorryAx`. -/
  | proved
  /-- Derived, free of `sorryAx`, from a cited `Literature` hypothesis. -/
  | cited
  /-- A precise statement with a disclosed `sorry`, believed true with a stated confidence. -/
  | frozen
  deriving Repr, DecidableEq, Inhabited

/-- Evidence for the statement `P`.  The constructor is the tier; the audit checks the claim. -/
inductive Evidence (P : Prop) : Type where
  /-- A kernel proof. -/
  | proved (h : P)
  /-- A proof from a cited hypothesis `L`, normally a `Literature.*` Prop. -/
  | cited (L : Prop) (h : L → P)
  /-- A `sorry` theorem: the statement is frozen, the proof is owed. -/
  | frozen (h : P)

/-- The tier an `Evidence` term claims. -/
def Evidence.tier {P : Prop} : Evidence P → Tier
  | .proved _ => .proved
  | .cited _ _ => .cited
  | .frozen _ => .frozen

/-- A known-false sibling.  Build one with `Barrier.proved`, `Barrier.cited` or `Barrier.frozen`
so the statement is inferred from the evidence. -/
structure Barrier where
  /-- The sibling object, in a few words. -/
  sibling : String
  /-- What is known about it, as a Lean statement. -/
  statement : Prop
  /-- The evidence for `statement`.  Its constructor is the tier. -/
  evidence : Evidence statement
  /-- The declarations carrying the evidence.  Each must occur in the barrier's value. -/
  decls : List Name
  /-- The mechanism shape this sibling refutes: a mechanism of this shape that does not fail on
  the sibling proves something false. -/
  guards : String

/-- A barrier settled by kernel proofs. -/
def Barrier.proved {P : Prop} (sibling : String) (h : P) (decls : List Name)
    (guards : String) : Barrier :=
  ⟨sibling, P, .proved h, decls, guards⟩

/-- A barrier settled from a cited hypothesis. -/
def Barrier.cited {P : Prop} (sibling : String) (L : Prop) (h : L → P) (decls : List Name)
    (guards : String) : Barrier :=
  ⟨sibling, P, .cited L h, decls, guards⟩

/-- A barrier whose statement is frozen with a disclosed `sorry`. -/
def Barrier.frozen {P : Prop} (sibling : String) (h : P) (decls : List Name)
    (guards : String) : Barrier :=
  ⟨sibling, P, .frozen h, decls, guards⟩

/-- The tier of a barrier. -/
def Barrier.tier (b : Barrier) : Tier := b.evidence.tier

/-- A frozen headline `sorry` and the barriers its mechanism must fail on. -/
structure CruxLink where
  /-- The crux: a declaration with a direct `sorry`. -/
  crux : Name
  /-- Names of `Barrier` definitions (at least one). -/
  barriers : List Name
  /-- How the mechanism must use something the sibling lacks. -/
  why : String

/-- An open `sorry` that is not a crux, with the reason no barrier applies. -/
structure Waiver where
  /-- The declaration with a direct `sorry`. -/
  decl : Name
  /-- Why it carries no barrier (a leaf, a literature-strength input, a refutation bet, …). -/
  reason : String

/-! ## The audit -/

/-- Whether `n`'s own value mentions `sorryAx` (a *direct* `sorry`, not one inherited). -/
def hasDirectSorry (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some ci => match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants.contains ``sorryAx
    | none => false
  | none => false

/-- Every non-internal declaration of a module under `pre` (imported or current) with a direct
`sorry`. -/
def directSorries (env : Environment) (pre : Name) : Array Name := Id.run do
  let mut out := #[]
  let names := env.header.moduleNames
  for h : i in [:env.header.moduleData.size] do
    if pre.isPrefixOf (names[i]?.getD .anonymous) then
      for n in env.header.moduleData[i].constNames do
        if !n.isInternal && hasDirectSorry env n then out := out.push n
  if pre.isPrefixOf env.mainModule then
    out := env.constants.foldStage2 (fun acc n _ =>
      if !n.isInternal && hasDirectSorry env n then acc.push n else acc) out
  return out

/-- Constants used by `n`'s value, looking through the auxiliary declarations
(`n._proof_1`, …) that the elaborator abstracts proofs into. -/
partial def usedDeep (env : Environment) (n : Name) : Array Name :=
  let direct := match env.find? n with
    | some ci => (ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
    | none => #[]
  direct.foldl (fun acc c =>
    if c.isInternal && n.isPrefixOf c then acc ++ usedDeep env c else acc.push c) #[]

/-- The audit's view of one barrier. -/
structure BarrierInfo where
  /-- The `Barrier` definition. -/
  name : Name
  /-- Its claimed tier. -/
  tier : Tier
  /-- Its evidence declarations. -/
  decls : List Name

/-- The audit.  Findings, one line each; empty means pass.

* each barrier names a declaration, every named declaration exists and occurs in the barrier's
  value, `proved`/`cited` barriers are `sorryAx`-free, and `frozen` ones still use `sorryAx`;
* each crux exists, has a direct `sorry`, names at least one barrier, all registered, and says
  why;
* each waiver exists, has a direct `sorry`, and gives a reason; nothing is both crux and waiver;
* every direct `sorry` under `NormalNumbers` is a crux, a waiver, or a frozen barrier's
  declaration. -/
def auditBarriers (bs : List BarrierInfo) (cs : List CruxLink) (ws : List Waiver)
    (sorries : Array Name) : CommandElabM (List String) := do
  let env ← getEnv
  let mut out : List String := []
  let regd := bs.map (·.name)
  let mut frozenDecls : List Name := []
  for b in bs do
    if b.decls.isEmpty then out := out ++ [s!"barrier {b.name} names no declaration"]
    let used := usedDeep env b.name
    let mut anySorry := false
    for d in b.decls do
      if !env.contains d then
        out := out ++ [s!"barrier {b.name}: declaration {d} does not exist"]
        continue
      if !used.contains d then
        out := out ++ [s!"barrier {b.name}: {d} does not occur in the barrier's evidence"]
      let axs ← collectAxioms d
      if axs.contains ``sorryAx then anySorry := true
    match b.tier with
    | .frozen =>
      frozenDecls := frozenDecls ++ b.decls
      if !anySorry && !b.decls.isEmpty then
        out := out ++ [s!"frozen barrier {b.name} is now sorry-free: promote it to Barrier.proved"]
    | t =>
      if anySorry then
        out := out ++ [s!"barrier {b.name} claims tier {repr t} but its evidence uses sorryAx"]
  for c in cs do
    if !env.contains c.crux then
      out := out ++ [s!"crux {c.crux} does not exist"]
    else if !sorries.contains c.crux then
      out := out ++ [s!"crux {c.crux} has no direct sorry: it is proved or moved; update the link"]
    if c.barriers.isEmpty then
      out := out ++ [s!"crux {c.crux} names no barrier"]
    for b in c.barriers do
      if !regd.contains b then
        out := out ++ [s!"crux {c.crux} names {b}, which is not a registered barrier"]
    if c.why.isEmpty then out := out ++ [s!"crux {c.crux} gives no reason"]
  for w in ws do
    if !env.contains w.decl then
      out := out ++ [s!"waiver {w.decl} does not exist"]
    else if !sorries.contains w.decl then
      out := out ++ [s!"waiver {w.decl} has no direct sorry: delete the waiver"]
    if w.reason.isEmpty then out := out ++ [s!"waiver {w.decl} gives no reason"]
    if cs.any (·.crux == w.decl) then
      out := out ++ [s!"{w.decl} is both a crux and a waiver"]
  for n in sorries do
    if !(cs.any (·.crux == n) || ws.any (·.decl == n) || frozenDecls.contains n) then
      out := out ++ [s!"open sorry {n} is untagged: link it to a barrier (a CruxLink) or record \
        why none applies (a Waiver)"]
  return out

/-- Evaluate one `Barrier` definition's erased view. -/
unsafe def evalBarrierInfo (n : Name) : TermElabM BarrierInfo := do
  let ty ← Term.elabType (← `(NormalNumbers.Barriers.BarrierInfo))
  let stx ← `((⟨$(quote n), (NormalNumbers.Barriers.Barrier.tier $(mkCIdent n)),
    ($(mkCIdent n)).decls⟩ : NormalNumbers.Barriers.BarrierInfo))
  Term.evalTerm BarrierInfo ty stx

/-- Evaluate the three registries. -/
unsafe def evalRegistries (bs cs ws : Term) :
    TermElabM (List Name × List CruxLink × List Waiver) := do
  let ty ← Term.elabType (← `(List Lean.Name × List NormalNumbers.Barriers.CruxLink ×
    List NormalNumbers.Barriers.Waiver))
  Term.evalTerm _ ty (← `(($bs, $cs, $ws)))

/-- `#barrier_audit barriers, cruxes, waivers` fails the build unless every open `sorry` in the
environment's `NormalNumbers` modules is a crux linked to a registered barrier, a waiver, or a
frozen barrier, and every barrier's tier is honest.  See `auditBarriers`.  Its scope is the
current environment, so the authoritative run is the one at the end of the root file
`NormalNumbers.lean`, which imports every module. -/
elab "#barrier_audit " bs:term ", " cs:term ", " ws:term : command => do
  let (bNames, cruxes, waivers) ← liftTermElabM (unsafe evalRegistries bs cs ws)
  let infos ← liftTermElabM (bNames.mapM fun n => unsafe evalBarrierInfo n)
  let env ← getEnv
  let sorries := directSorries env `NormalNumbers
  let problems ← auditBarriers infos cruxes waivers sorries
  if problems.isEmpty then
    let count (t : Tier) := (infos.filter (·.tier == t)).length
    logInfo m!"barrier audit: {infos.length} barriers ({count .proved} proved, \
      {count .cited} cited, {count .frozen} frozen); {cruxes.length} cruxes linked, \
      {waivers.length} waived, {sorries.size} open sorries scanned"
  else
    throwError "barrier audit failed ({problems.length}):\n{"\n".intercalate problems}"

end NormalNumbers.Barriers
