import PMTree8Branch1
import PMTree8Branch2
import PMTree8Branch3
import PMTree8Branch4
import PMTree8Branch5
import PMTree8Branch6
import PMTree8Branch7

open MonochromaticQuantumGraph

namespace D19Round20

/-- Fully expanded recursive matching tree on eight vertices. -/
def pmTree8 {K : Type} [Semiring K]
    (W : WeightsN 8 3 K) (ι : Fin 8 → Fin 3) : K :=
  ([
    pmTree8Branch1 W ι,
    pmTree8Branch2 W ι,
    pmTree8Branch3 W ι,
    pmTree8Branch4 W ι,
    pmTree8Branch5 W ι,
    pmTree8Branch6 W ι,
    pmTree8Branch7 W ι
  ] : List K).sum

set_option maxRecDepth 100000 in
@[simp] theorem pmSumN_eight_eq_tree {K : Type} [Semiring K]
    (W : WeightsN 8 3 K) (ι : Fin 8 → Fin 3) :
    pmSumN 8 3 W ι = pmTree8 W ι := by
  rfl

end D19Round20
