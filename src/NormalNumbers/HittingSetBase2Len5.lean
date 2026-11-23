/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetBase2Len5Core
import NormalNumbers.HittingSetBase2Len5Cert0
import NormalNumbers.HittingSetBase2Len5Cert1
import NormalNumbers.HittingSetBase2Len5Cert2
import NormalNumbers.HittingSetBase2Len5Cert3
import NormalNumbers.HittingSetBase2Len5Cert4
import NormalNumbers.HittingSetBase2Len5Cert5
import NormalNumbers.HittingSetBase2Len5Cert6
import NormalNumbers.HittingSetBase2Len5Cert7
import NormalNumbers.HittingSetBase2Len5Cert8
import NormalNumbers.HittingSetBase2Len5Cert9
import NormalNumbers.HittingSetBase2Len5Cert10
import NormalNumbers.HittingSetBase2Len5Cert11
import NormalNumbers.HittingSetBase2Len5Cert12
import NormalNumbers.HittingSetBase2Len5Cert13
import NormalNumbers.HittingSetBase2Len5Cert14
import NormalNumbers.HittingSetBase2Len5Cert15
import NormalNumbers.HittingSetBase2Len5Cert16
import NormalNumbers.HittingSetBase2Len5Cert17
import NormalNumbers.HittingSetBase2Len5Cert18
import NormalNumbers.HittingSetBase2Len5Cert19
import NormalNumbers.HittingSetBase2Len5Cert20
import NormalNumbers.HittingSetBase2Len5Cert21
import NormalNumbers.HittingSetBase2Len5Cert22
import NormalNumbers.HittingSetBase2Len5Cert23
import NormalNumbers.HittingSetBase2Len5Cert24
import NormalNumbers.HittingSetBase2Len5Cert25
import NormalNumbers.HittingSetBase2Len5Cert26
import NormalNumbers.HittingSetBase2Len5Cert27
import NormalNumbers.HittingSetBase2Len5Cert28
import NormalNumbers.HittingSetBase2Len5Cert29
import NormalNumbers.HittingSetBase2Len5Cert30
import NormalNumbers.HittingSetBase2Len5Cert31

/-!
# `S(2,5) ≤ 20` — the assembly

See `HittingSetBase2Len5Core.lean` for the reduction and the run-compressed reachability sweep; the certificates are in `HittingSetBase2Len5Cert*.lean`.
-/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

/-- The section hypothesis of `signed_engine_g_single_reduced`, from `h25_section`. -/
theorem h25_sec (X : ℝ) (w : List ℕ) (hw : w.length = 5) (m : ℕ) :
    h25Lget (h25idx (gfamState 2 (chansOfW h25ms w) X 0 m))
        = gfamState 2 (chansOfW h25ms w) X 0 m
      ∧ h25idx (gfamState 2 (chansOfW h25ms w) X 0 m) < 5328 := by
  have hms : ∀ a ∈ h25ms, 1 ≤ a := by decide
  have hdvd : ∀ a ∈ h25ms, ∀ j, j ≤ 5 - 1 → a * 2 ^ j ∣ h25N := by decide
  have ht1 : Int.fract (X * ((2 : ℕ) : ℝ) ^ m) < 1 := Int.fract_lt_one _
  rw [gfamState_window 2 (by norm_num) h25ms hms w 5 hw h25N (by norm_num [h25N]) hdvd X m]
  refine h25_section _ ?_
  have hN0 : (0 : ℝ) < (h25N : ℝ) := by norm_num [h25N]
  have hfl : ⌊(h25N : ℝ) * Int.fract (X * ((2 : ℕ) : ℝ) ^ m)⌋ < (h25N : ℤ) := by
    apply Int.floor_lt.2
    push_cast
    calc (h25N : ℝ) * Int.fract (X * ((2 : ℕ) : ℝ) ^ m) < (h25N : ℝ) * 1 :=
          mul_lt_mul_of_pos_left ht1 hN0
      _ = (h25N : ℝ) := by ring
  have hpos' : 0 < h25N := by norm_num [h25N]
  omega

/-- **`S(2,5) ≤ 20`.** -/
theorem hitting_2_5_twenty : Literature.IsHittingSet 2 5 {1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 41} := by
  intro α hα w hw hd
  have hpos : ∀ v : List ℕ, ∀ ch ∈ chansOfW h25ms v, 1 ≤ ch.posSum := by
    intro v ch hch
    simp only [chansOfW, h25ms, List.mem_map] at hch
    obtain ⟨a, ha, rfl⟩ := hch
    simp only [ZChannel.posSum]
    fin_cases ha <;> decide
  have hell : ∀ v : List ℕ, v.length = 5 → ∀ ch ∈ chansOfW h25ms v, 1 ≤ ch.ell := by
    intro v hv ch hch
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    simp [ZChannel.ell, hv]
  have hword : ∀ v : List ℕ, (∀ c ∈ v, c < 2) → ∀ ch ∈ chansOfW h25ms v, ∀ c ∈ ch.word, c < 2 := by
    intro v hv ch hch c hc
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    exact hv c hc
  obtain ⟨d0, d1, d2, d3, d4, rfl⟩ : ∃ d0 d1 d2 d3 d4, w = [d0, d1, d2, d3, d4] := by
    rcases w with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | ⟨d4, _ | ⟨z, t⟩⟩⟩⟩⟩⟩ <;> simp at hw
    exact ⟨d0, d1, d2, d3, d4, rfl⟩
  have hltd0 : d0 < 2 := hd d0 (by simp)
  have hltd1 : d1 < 2 := hd d1 (by simp)
  have hltd2 : d2 < 2 := hd d2 (by simp)
  have hltd3 : d3 < 2 := hd d3 (by simp)
  have hltd4 : d4 < 2 := hd d4 (by simp)
  have key : ∃ ch ∈ chansOfW h25ms [d0, d1, d2, d3, d4],
      ∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (ch.a * α) ch.word n := by
    interval_cases d0 <;> interval_cases d1 <;> interval_cases d2 <;> interval_cases d3 <;> interval_cases d4
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 0, 0, 0, 0])
        h25Lget h25idx h25w00000_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 0, 0, 0, 0] rfl m).2)
        (fun m => (h25_sec α [0, 0, 0, 0, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 0, 0, 0, 1])
        h25Lget h25idx h25w00001_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 0, 0, 0, 1] rfl m).2)
        (fun m => (h25_sec α [0, 0, 0, 0, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 0, 0, 1, 0])
        h25Lget h25idx h25w00010_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 0, 0, 1, 0] rfl m).2)
        (fun m => (h25_sec α [0, 0, 0, 1, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 0, 0, 1, 1])
        h25Lget h25idx h25w00011_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 0, 0, 1, 1] rfl m).2)
        (fun m => (h25_sec α [0, 0, 0, 1, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 0, 1, 0, 0])
        h25Lget h25idx h25w00100_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 0, 1, 0, 0] rfl m).2)
        (fun m => (h25_sec α [0, 0, 1, 0, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 0, 1, 0, 1])
        h25Lget h25idx h25w00101_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 0, 1, 0, 1] rfl m).2)
        (fun m => (h25_sec α [0, 0, 1, 0, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 0, 1, 1, 0])
        h25Lget h25idx h25w00110_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 0, 1, 1, 0] rfl m).2)
        (fun m => (h25_sec α [0, 0, 1, 1, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 0, 1, 1, 1])
        h25Lget h25idx h25w00111_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 0, 1, 1, 1] rfl m).2)
        (fun m => (h25_sec α [0, 0, 1, 1, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 1, 0, 0, 0])
        h25Lget h25idx h25w01000_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 1, 0, 0, 0] rfl m).2)
        (fun m => (h25_sec α [0, 1, 0, 0, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 1, 0, 0, 1])
        h25Lget h25idx h25w01001_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 1, 0, 0, 1] rfl m).2)
        (fun m => (h25_sec α [0, 1, 0, 0, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 1, 0, 1, 0])
        h25Lget h25idx h25w01010_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 1, 0, 1, 0] rfl m).2)
        (fun m => (h25_sec α [0, 1, 0, 1, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 1, 0, 1, 1])
        h25Lget h25idx h25w01011_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 1, 0, 1, 1] rfl m).2)
        (fun m => (h25_sec α [0, 1, 0, 1, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 1, 1, 0, 0])
        h25Lget h25idx h25w01100_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 1, 1, 0, 0] rfl m).2)
        (fun m => (h25_sec α [0, 1, 1, 0, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 1, 1, 0, 1])
        h25Lget h25idx h25w01101_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 1, 1, 0, 1] rfl m).2)
        (fun m => (h25_sec α [0, 1, 1, 0, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 1, 1, 1, 0])
        h25Lget h25idx h25w01110_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 1, 1, 1, 0] rfl m).2)
        (fun m => (h25_sec α [0, 1, 1, 1, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [0, 1, 1, 1, 1])
        h25Lget h25idx h25w01111_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [0, 1, 1, 1, 1] rfl m).2)
        (fun m => (h25_sec α [0, 1, 1, 1, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 0, 0, 0, 0])
        h25Lget h25idx h25w10000_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 0, 0, 0, 0] rfl m).2)
        (fun m => (h25_sec α [1, 0, 0, 0, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 0, 0, 0, 1])
        h25Lget h25idx h25w10001_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 0, 0, 0, 1] rfl m).2)
        (fun m => (h25_sec α [1, 0, 0, 0, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 0, 0, 1, 0])
        h25Lget h25idx h25w10010_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 0, 0, 1, 0] rfl m).2)
        (fun m => (h25_sec α [1, 0, 0, 1, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 0, 0, 1, 1])
        h25Lget h25idx h25w10011_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 0, 0, 1, 1] rfl m).2)
        (fun m => (h25_sec α [1, 0, 0, 1, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 0, 1, 0, 0])
        h25Lget h25idx h25w10100_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 0, 1, 0, 0] rfl m).2)
        (fun m => (h25_sec α [1, 0, 1, 0, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 0, 1, 0, 1])
        h25Lget h25idx h25w10101_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 0, 1, 0, 1] rfl m).2)
        (fun m => (h25_sec α [1, 0, 1, 0, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 0, 1, 1, 0])
        h25Lget h25idx h25w10110_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 0, 1, 1, 0] rfl m).2)
        (fun m => (h25_sec α [1, 0, 1, 1, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 0, 1, 1, 1])
        h25Lget h25idx h25w10111_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 0, 1, 1, 1] rfl m).2)
        (fun m => (h25_sec α [1, 0, 1, 1, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 1, 0, 0, 0])
        h25Lget h25idx h25w11000_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 1, 0, 0, 0] rfl m).2)
        (fun m => (h25_sec α [1, 1, 0, 0, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 1, 0, 0, 1])
        h25Lget h25idx h25w11001_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 1, 0, 0, 1] rfl m).2)
        (fun m => (h25_sec α [1, 1, 0, 0, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 1, 0, 1, 0])
        h25Lget h25idx h25w11010_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 1, 0, 1, 0] rfl m).2)
        (fun m => (h25_sec α [1, 1, 0, 1, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 1, 0, 1, 1])
        h25Lget h25idx h25w11011_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 1, 0, 1, 1] rfl m).2)
        (fun m => (h25_sec α [1, 1, 0, 1, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 1, 1, 0, 0])
        h25Lget h25idx h25w11100_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 1, 1, 0, 0] rfl m).2)
        (fun m => (h25_sec α [1, 1, 1, 0, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 1, 1, 0, 1])
        h25Lget h25idx h25w11101_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 1, 1, 0, 1] rfl m).2)
        (fun m => (h25_sec α [1, 1, 1, 0, 1] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 1, 1, 1, 0])
        h25Lget h25idx h25w11110_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 1, 1, 1, 0] rfl m).2)
        (fun m => (h25_sec α [1, 1, 1, 1, 0] rfl m).1)
    · exact signed_engine_g_single_reduced 2 (by norm_num) (chansOfW h25ms [1, 1, 1, 1, 1])
        h25Lget h25idx h25w11111_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => (h25_sec α [1, 1, 1, 1, 1] rfl m).2)
        (fun m => (h25_sec α [1, 1, 1, 1, 1] rfl m).1)
  obtain ⟨ch, hch, hio⟩ := key
  simp only [chansOfW, h25ms, List.map_cons, List.map_nil] at hch
  fin_cases hch
  · exact ⟨1, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨3, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨5, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨7, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨9, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨11, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨13, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨15, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨17, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨19, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨21, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨23, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨25, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨27, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨29, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨31, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨33, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨35, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨37, by simp, by norm_num, by simpa using hio⟩
  · exact ⟨41, by simp, by norm_num, by simpa using hio⟩

end NormalNumbers.Adder
