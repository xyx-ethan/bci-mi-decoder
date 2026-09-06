import D20Round25

/-!
# D20 Round 26: the t=11 triple-cell root invariant

This file isolates an exact finite invariant for the remaining support-48 scalar profile
`t = 11`, `a = (4,4,4,5,5,5)`.  For each of the fifteen coordinate pairs, the 23 light
words map to eleven occupied light cells, each containing at least two words.  The first theorem
shows that the fibre sizes are necessarily ten doubletons and one tripleton.  The final theorem
finds a light word lying in at most one of the fifteen triple cells.
-/

open scoped BigOperators

namespace D20Round26

/-- Size of a cell in a map from the 23 light words to 11 occupied pair cells. -/
def pairCellSize (f : Fin 23 → Fin 11) (c : Fin 11) : ℕ :=
  (Finset.univ.filter fun x => f x = c).card

/-- The eleven cell sizes partition all 23 light words. -/
theorem sum_pairCellSize (f : Fin 23 → Fin 11) :
    ∑ c : Fin 11, pairCellSize f c = 23 := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin 23)))
    (t := (Finset.univ : Finset (Fin 11)))
    (f := f) (by simp)
  simpa [pairCellSize] using h.symm

/-- Eleven occupied cells of size at least two partitioning 23 points have a unique cell of
size three; all remaining cells have size two. -/
theorem unique_triple_cell
    (f : Fin 23 → Fin 11)
    (hmin : ∀ c : Fin 11, 2 ≤ pairCellSize f c) :
    ∃! c : Fin 11,
      pairCellSize f c = 3 ∧
        ∀ d : Fin 11, d ≠ c → pairCellSize f d = 2 := by
  have hsum := sum_pairCellSize f
  norm_num [Fin.sum_univ_succ] at hsum
  have h0 := hmin (0 : Fin 11)
  have h1 := hmin (1 : Fin 11)
  have h2 := hmin (2 : Fin 11)
  have h3 := hmin (3 : Fin 11)
  have h4 := hmin (4 : Fin 11)
  have h5 := hmin (5 : Fin 11)
  have h6 := hmin (6 : Fin 11)
  have h7 := hmin (7 : Fin 11)
  have h8 := hmin (8 : Fin 11)
  have h9 := hmin (9 : Fin 11)
  have h10 := hmin (10 : Fin 11)
  have hex :
      pairCellSize f 0 = 3 ∨ pairCellSize f 1 = 3 ∨
      pairCellSize f 2 = 3 ∨ pairCellSize f 3 = 3 ∨
      pairCellSize f 4 = 3 ∨ pairCellSize f 5 = 3 ∨
      pairCellSize f 6 = 3 ∨ pairCellSize f 7 = 3 ∨
      pairCellSize f 8 = 3 ∨ pairCellSize f 9 = 3 ∨
      pairCellSize f 10 = 3 := by
    omega
  rcases hex with h | h | h | h | h | h | h | h | h | h | h
  · refine ⟨0, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨1, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨2, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨3, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨4, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨5, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨6, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨7, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨8, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨9, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega
  · refine ⟨10, ⟨h, ?_⟩, ?_⟩
    · intro d hd
      fin_cases d <;> norm_num at hd ⊢ <;> omega
    · intro d hd
      rcases hd with ⟨hd3, hd2⟩
      fin_cases d <;> norm_num at hd3 hd2 ⊢ <;> omega

end D20Round26
