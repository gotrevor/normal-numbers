# Coons 2014 — pin note (read 2026-10-05, the parts cited)

M. Coons, *An arithmetical excursion via Stoneham numbers*, J. Aust. Math. Soc. 96 (2014) 303-315,
arXiv:1212.3449.  PDF alongside (gitignored).

- Intro, p. 1: *"Transcendence of α_{b,c} follows easily by Mahler's method; the interested reader
  can see the details Appendix A."*  Also quotes Bailey–Crandall 2002: `α_{b,c}` is `b`-normal for
  all coprime `b, c ≥ 2`.
- **Appendix A**: `F_c(x) = Σ_{n≥1} x^(cⁿ)/cⁿ` is a Mahler function, transcendental over `ℂ(x)`
  (Nishioka 1985, Thm A.1), so `α_{b,c} = F_c(1/b)` is transcendental (Mahler, via Nishioka's
  monograph, Thm A.2).
- Used by: `LandscapeGrid.coons_stoneham23_transcendental`.
