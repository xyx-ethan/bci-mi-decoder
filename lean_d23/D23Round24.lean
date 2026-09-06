import D23Round23

namespace D23Round24

open D23Round21 D23Round22 D23Round23

/-- If the scalar parameter satisfies `q ≥ 2p`, the Round-21 full-rank estimate
improves from `|W|² < 16` to `|W|² < 4`. -/
theorem ratioTwo_fullRank_norm_lt_four
    (p q A B wx wy tx ty rx ry sx sy : ℤ)
    (hp : 0 < p)
    (h2pq : 2 * p ≤ q)
    (hbeta : normSq A B = p * p)
    (hdet : detZ rx ry sx sy ≠ 0)
    (henergy :
      q * normSq wx wy + normSq tx ty +
          2 * normSq rx ry + 2 * normSq sx sy =
        4 * (A * wx + B * wy)) :
    normSq wx wy < 4 := by
  have hpq : p ≤ q := by nlinarith
  obtain ⟨hwpos, _⟩ := fullRank_scalar_norm_lt_sixteen
    p q A B wx wy tx ty rx ry sx sy hp hpq hbeta hdet henergy
  have hrne : normSq rx ry ≠ 0 := by
    intro hr0
    obtain ⟨hrx, hry⟩ := (normSq_eq_zero_iff rx ry).mp hr0
    apply hdet
    simp [detZ, hrx, hry]
  have hsne : normSq sx sy ≠ 0 := by
    intro hs0
    obtain ⟨hsx, hsy⟩ := (normSq_eq_zero_iff sx sy).mp hs0
    apply hdet
    simp [detZ, hsx, hsy]
  have hrpos : 0 < normSq rx ry := by
    have h := normSq_nonneg rx ry
    omega
  have hspos : 0 < normSq sx sy := by
    have h := normSq_nonneg sx sy
    omega
  have ht_nonneg : 0 ≤ normSq tx ty := normSq_nonneg tx ty
  have hrespos :
      0 < normSq tx ty + 2 * normSq rx ry + 2 * normSq sx sy := by
    nlinarith
  have hqpos : 0 < q := by nlinarith
  have hstrict :
      q * normSq wx wy < 4 * (A * wx + B * wy) := by
    nlinarith [henergy]
  have hqWpos : 0 < q * normSq wx wy := mul_pos hqpos hwpos
  have hinnerpos : 0 < A * wx + B * wy := by
    nlinarith
  have hcauchy :
      (A * wx + B * wy) * (A * wx + B * wy) ≤
        (p * p) * normSq wx wy := by
    have hcross : 0 ≤ (A * wy - B * wx) * (A * wy - B * wx) := by
      nlinarith [sq_nonneg (A * wy - B * wx)]
    simp only [normSq] at hbeta ⊢
    nlinarith
  let X : ℤ := q * normSq wx wy
  let Y : ℤ := 4 * (A * wx + B * wy)
  have hXY : X < Y := by simpa [X, Y] using hstrict
  have hXpos : 0 < X := by simpa [X] using hqWpos
  have hYpos : 0 < Y := by
    dsimp [Y]
    nlinarith
  have hfactorpos : 0 < (Y - X) * (Y + X) := by
    apply mul_pos
    · omega
    · omega
  have hsquare : X * X < Y * Y := by
    nlinarith
  have hsquare_bound :
      (q * normSq wx wy) * (q * normSq wx wy) <
        16 * (p * p) * normSq wx wy := by
    dsimp [X, Y] at hsquare
    nlinarith [hcauchy]
  have hNnonneg : 0 ≤ normSq wx wy := normSq_nonneg wx wy
  have h2pnonneg : 0 ≤ 2 * p := by nlinarith
  have hq2ge0 : (2 * p) * (2 * p) ≤ q * q :=
    mul_self_le_mul_self h2pnonneg h2pq
  have hq2ge : 4 * (p * p) ≤ q * q := by
    nlinarith [hq2ge0]
  by_contra hnot
  have hNge : 4 ≤ normSq wx wy := by omega
  have hNN : 4 * normSq wx wy ≤ normSq wx wy * normSq wx wy := by
    nlinarith
  have hpcoef : 0 ≤ 4 * (p * p) := by positivity
  have hmulN := mul_le_mul_of_nonneg_left hNN hpcoef
  have hN2nonneg : 0 ≤ normSq wx wy * normSq wx wy := by positivity
  have hmulQ := mul_le_mul_of_nonneg_right hq2ge hN2nonneg
  nlinarith [hsquare_bound, hmulN, hmulQ]

/-- In the inert-prime branch, once `q ≥ 2p` the full-rank scalar system forces
`|W|² = 1` and, integrally, the stronger gap `q + 4 ≤ 4p`. -/
theorem inertPrime_ratioTwo_unit_and_gap
    (p : ℕ) (q A B wx wy tx ty rx ry sx sy : ℤ)
    (hp : p.Prime)
    (hmod : p % 4 = 3)
    (h2pq : 2 * (p : ℤ) ≤ q)
    (hbeta : normSq A B = (p : ℤ) * (p : ℤ))
    (hdet : detZ rx ry sx sy ≠ 0)
    (henergy :
      q * normSq wx wy + normSq tx ty +
          2 * normSq rx ry + 2 * normSq sx sy =
        4 * (A * wx + B * wy)) :
    normSq wx wy = 1 ∧ q + 4 ≤ 4 * (p : ℤ) := by
  have hpInt : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  have hpq : (p : ℤ) ≤ q := by nlinarith
  have haxis := inertPrime_beta_axis p A B hp hmod hbeta
  have hlt4 := ratioTwo_fullRank_norm_lt_four
    (p : ℤ) q A B wx wy tx ty rx ry sx sy
    hpInt h2pq hbeta hdet henergy
  have hcases := inertPrime_fullRank_scalar_norm_cases
    p q A B wx wy tx ty rx ry sx sy hp hmod hpq hbeta hdet henergy
  have hN12 : normSq wx wy = 1 ∨ normSq wx wy = 2 := by
    rcases hcases with h1 | h2 | h4 | h5 | h9 | h10
    · exact Or.inl h1
    · exact Or.inr h2
    · omega
    · omega
    · omega
    · omega
  have hrne : normSq rx ry ≠ 0 := by
    intro hr0
    obtain ⟨hrx, hry⟩ := (normSq_eq_zero_iff rx ry).mp hr0
    apply hdet
    simp [detZ, hrx, hry]
  have hsne : normSq sx sy ≠ 0 := by
    intro hs0
    obtain ⟨hsx, hsy⟩ := (normSq_eq_zero_iff sx sy).mp hs0
    apply hdet
    simp [detZ, hsx, hsy]
  have hrpos : 0 < normSq rx ry := by
    have h := normSq_nonneg rx ry
    omega
  have hspos : 0 < normSq sx sy := by
    have h := normSq_nonneg sx sy
    omega
  have ht_nonneg : 0 ≤ normSq tx ty := normSq_nonneg tx ty
  have hresge4 :
      4 ≤ normSq tx ty + 2 * normSq rx ry + 2 * normSq sx sy := by
    have hrge1 : 1 ≤ normSq rx ry := by omega
    have hsge1 : 1 ≤ normSq sx sy := by omega
    nlinarith
  have hN2false : normSq wx wy ≠ 2 := by
    intro hN2
    let D : ℤ := A * wx + B * wy
    have hDsq : D * D ≤ (p : ℤ) * (p : ℤ) := by
      rcases haxis with hA | hB
      · subst A
        have hb2 : B * B = (p : ℤ) * (p : ℤ) := by
          simpa [normSq] using hbeta
        have hwylo : -1 ≤ wy := by
          by_contra h
          have hle : wy ≤ -2 := by omega
          simp only [normSq] at hN2
          nlinarith [sq_nonneg wx]
        have hwyhi : wy ≤ 1 := by
          by_contra h
          have hge : 2 ≤ wy := by omega
          simp only [normSq] at hN2
          nlinarith [sq_nonneg wx]
        have hwy2 : wy * wy ≤ 1 := by nlinarith
        have hB2nonneg : 0 ≤ B * B := by positivity
        have hmul := mul_le_mul_of_nonneg_left hwy2 hB2nonneg
        dsimp [D]
        calc
          (B * wy) * (B * wy) = (B * B) * (wy * wy) := by ring
          _ ≤ (B * B) * 1 := hmul
          _ = (p : ℤ) * (p : ℤ) := by rw [hb2]; ring
      · subst B
        have ha2 : A * A = (p : ℤ) * (p : ℤ) := by
          simpa [normSq] using hbeta
        have hwxlo : -1 ≤ wx := by
          by_contra h
          have hle : wx ≤ -2 := by omega
          simp only [normSq] at hN2
          nlinarith [sq_nonneg wy]
        have hwxhi : wx ≤ 1 := by
          by_contra h
          have hge : 2 ≤ wx := by omega
          simp only [normSq] at hN2
          nlinarith [sq_nonneg wy]
        have hwx2 : wx * wx ≤ 1 := by nlinarith
        have hA2nonneg : 0 ≤ A * A := by positivity
        have hmul := mul_le_mul_of_nonneg_left hwx2 hA2nonneg
        dsimp [D]
        calc
          (A * wx) * (A * wx) = (A * A) * (wx * wx) := by ring
          _ ≤ (A * A) * 1 := hmul
          _ = (p : ℤ) * (p : ℤ) := by rw [ha2]; ring
    have hDgt : (p : ℤ) < D := by
      dsimp [D]
      nlinarith [henergy, hresge4]
    have hDpos : 0 < D := lt_trans hpInt hDgt
    have hp2lt : (p : ℤ) * (p : ℤ) < D * D := by
      nlinarith
    exact (not_lt_of_ge hDsq) hp2lt
  have hN1 : normSq wx wy = 1 := hN12.resolve_right hN2false
  have hcauchy :
      (A * wx + B * wy) * (A * wx + B * wy) ≤
        ((p : ℤ) * (p : ℤ)) * normSq wx wy := by
    have hcross : 0 ≤ (A * wy - B * wx) * (A * wy - B * wx) := by
      nlinarith [sq_nonneg (A * wy - B * wx)]
    simp only [normSq] at hbeta ⊢
    nlinarith
  have hDsq1 :
      (A * wx + B * wy) * (A * wx + B * wy) ≤
        (p : ℤ) * (p : ℤ) := by
    rw [hN1] at hcauchy
    simpa using hcauchy
  have hDpos : 0 < A * wx + B * wy := by
    nlinarith [henergy, hresge4]
  have hDle : A * wx + B * wy ≤ (p : ℤ) := by
    nlinarith
  constructor
  · exact hN1
  · rw [hN1] at henergy
    nlinarith [henergy, hresge4, hDle]

/-- The ratio-window theorem immediately excludes the full-rank scalar branch
when `q ≥ 4p`. -/
theorem inertPrime_ratioFour_no_fullRank_scalar
    (p : ℕ) (q A B wx wy tx ty rx ry sx sy : ℤ)
    (hp : p.Prime)
    (hmod : p % 4 = 3)
    (h4pq : 4 * (p : ℤ) ≤ q)
    (hbeta : normSq A B = (p : ℤ) * (p : ℤ))
    (hdet : detZ rx ry sx sy ≠ 0)
    (henergy :
      q * normSq wx wy + normSq tx ty +
          2 * normSq rx ry + 2 * normSq sx sy =
        4 * (A * wx + B * wy)) : False := by
  have h2pq : 2 * (p : ℤ) ≤ q := by nlinarith
  obtain ⟨_, hgap⟩ := inertPrime_ratioTwo_unit_and_gap
    p q A B wx wy tx ty rx ry sx sy hp hmod h2pq hbeta hdet henergy
  nlinarith

/-- Kernel-computable count of Gaussian integers with squared norm exactly one. -/
theorem unitGaussian_count_4 :
    ((List.range 3).flatMap fun i =>
      (List.range 3).map fun j =>
        ((i : ℤ) - 1, (j : ℤ) - 1)).countP
          (fun z => decide (normSq z.1 z.2 = 1)) = 4 := by
  decide

end D23Round24
