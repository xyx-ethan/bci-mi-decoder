import FormalConjectures.Paper.MonochromaticQuantumGraph

open MonochromaticQuantumGraph

namespace D19Round20

/-- Fully expanded recursive matching tree on six vertices. -/
def pmTree6 {K : Type} [Semiring K]
    (W : WeightsN 6 3 K) (ι : Fin 6 → Fin 3) : K :=
  ([
    W (mkEdge (N := 6) (D := 3) 0 1 (ι 0) (ι 1)) * (([
            W (mkEdge (N := 6) (D := 3) 2 3 (ι 2) (ι 3)) * (([
                        W (mkEdge (N := 6) (D := 3) 4 5 (ι 4) (ι 5)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 2 4 (ι 2) (ι 4)) * (([
                        W (mkEdge (N := 6) (D := 3) 3 5 (ι 3) (ι 5)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 2 5 (ι 2) (ι 5)) * (([
                        W (mkEdge (N := 6) (D := 3) 3 4 (ι 3) (ι 4)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum),
    W (mkEdge (N := 6) (D := 3) 0 2 (ι 0) (ι 2)) * (([
            W (mkEdge (N := 6) (D := 3) 1 3 (ι 1) (ι 3)) * (([
                        W (mkEdge (N := 6) (D := 3) 4 5 (ι 4) (ι 5)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 1 4 (ι 1) (ι 4)) * (([
                        W (mkEdge (N := 6) (D := 3) 3 5 (ι 3) (ι 5)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 1 5 (ι 1) (ι 5)) * (([
                        W (mkEdge (N := 6) (D := 3) 3 4 (ι 3) (ι 4)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum),
    W (mkEdge (N := 6) (D := 3) 0 3 (ι 0) (ι 3)) * (([
            W (mkEdge (N := 6) (D := 3) 1 2 (ι 1) (ι 2)) * (([
                        W (mkEdge (N := 6) (D := 3) 4 5 (ι 4) (ι 5)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 1 4 (ι 1) (ι 4)) * (([
                        W (mkEdge (N := 6) (D := 3) 2 5 (ι 2) (ι 5)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 1 5 (ι 1) (ι 5)) * (([
                        W (mkEdge (N := 6) (D := 3) 2 4 (ι 2) (ι 4)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum),
    W (mkEdge (N := 6) (D := 3) 0 4 (ι 0) (ι 4)) * (([
            W (mkEdge (N := 6) (D := 3) 1 2 (ι 1) (ι 2)) * (([
                        W (mkEdge (N := 6) (D := 3) 3 5 (ι 3) (ι 5)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 1 3 (ι 1) (ι 3)) * (([
                        W (mkEdge (N := 6) (D := 3) 2 5 (ι 2) (ι 5)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 1 5 (ι 1) (ι 5)) * (([
                        W (mkEdge (N := 6) (D := 3) 2 3 (ι 2) (ι 3)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum),
    W (mkEdge (N := 6) (D := 3) 0 5 (ι 0) (ι 5)) * (([
            W (mkEdge (N := 6) (D := 3) 1 2 (ι 1) (ι 2)) * (([
                        W (mkEdge (N := 6) (D := 3) 3 4 (ι 3) (ι 4)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 1 3 (ι 1) (ι 3)) * (([
                        W (mkEdge (N := 6) (D := 3) 2 4 (ι 2) (ι 4)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 6) (D := 3) 1 4 (ι 1) (ι 4)) * (([
                        W (mkEdge (N := 6) (D := 3) 2 3 (ι 2) (ι 3)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum)
  ] : List K).sum

set_option maxRecDepth 100000 in
@[simp] theorem pmSumN_six_eq_tree {K : Type} [Semiring K]
    (W : WeightsN 6 3 K) (ι : Fin 6 → Fin 3) :
    pmSumN 6 3 W ι = pmTree6 W ι := by
  rfl

end D19Round20
