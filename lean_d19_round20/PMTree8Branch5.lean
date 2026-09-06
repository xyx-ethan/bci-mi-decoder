import FormalConjectures.Paper.MonochromaticQuantumGraph

open MonochromaticQuantumGraph

namespace D19Round20

/-- Top-level branch in which vertex `0` is matched with vertex `5`. -/
def pmTree8Branch5 {K : Type} [Semiring K]
    (W : WeightsN 8 3 K) (ι : Fin 8 → Fin 3) : K :=
  W (mkEdge (N := 8) (D := 3) 0 5 (ι 0) (ι 5)) * (([
    W (mkEdge (N := 8) (D := 3) 1 2 (ι 1) (ι 2)) * (([
            W (mkEdge (N := 8) (D := 3) 3 4 (ι 3) (ι 4)) * (([
                        W (mkEdge (N := 8) (D := 3) 6 7 (ι 6) (ι 7)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 3 6 (ι 3) (ι 6)) * (([
                        W (mkEdge (N := 8) (D := 3) 4 7 (ι 4) (ι 7)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 3 7 (ι 3) (ι 7)) * (([
                        W (mkEdge (N := 8) (D := 3) 4 6 (ι 4) (ι 6)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum),
    W (mkEdge (N := 8) (D := 3) 1 3 (ι 1) (ι 3)) * (([
            W (mkEdge (N := 8) (D := 3) 2 4 (ι 2) (ι 4)) * (([
                        W (mkEdge (N := 8) (D := 3) 6 7 (ι 6) (ι 7)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 2 6 (ι 2) (ι 6)) * (([
                        W (mkEdge (N := 8) (D := 3) 4 7 (ι 4) (ι 7)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 2 7 (ι 2) (ι 7)) * (([
                        W (mkEdge (N := 8) (D := 3) 4 6 (ι 4) (ι 6)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum),
    W (mkEdge (N := 8) (D := 3) 1 4 (ι 1) (ι 4)) * (([
            W (mkEdge (N := 8) (D := 3) 2 3 (ι 2) (ι 3)) * (([
                        W (mkEdge (N := 8) (D := 3) 6 7 (ι 6) (ι 7)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 2 6 (ι 2) (ι 6)) * (([
                        W (mkEdge (N := 8) (D := 3) 3 7 (ι 3) (ι 7)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 2 7 (ι 2) (ι 7)) * (([
                        W (mkEdge (N := 8) (D := 3) 3 6 (ι 3) (ι 6)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum),
    W (mkEdge (N := 8) (D := 3) 1 6 (ι 1) (ι 6)) * (([
            W (mkEdge (N := 8) (D := 3) 2 3 (ι 2) (ι 3)) * (([
                        W (mkEdge (N := 8) (D := 3) 4 7 (ι 4) (ι 7)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 2 4 (ι 2) (ι 4)) * (([
                        W (mkEdge (N := 8) (D := 3) 3 7 (ι 3) (ι 7)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 2 7 (ι 2) (ι 7)) * (([
                        W (mkEdge (N := 8) (D := 3) 3 4 (ι 3) (ι 4)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum),
    W (mkEdge (N := 8) (D := 3) 1 7 (ι 1) (ι 7)) * (([
            W (mkEdge (N := 8) (D := 3) 2 3 (ι 2) (ι 3)) * (([
                        W (mkEdge (N := 8) (D := 3) 4 6 (ι 4) (ι 6)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 2 4 (ι 2) (ι 4)) * (([
                        W (mkEdge (N := 8) (D := 3) 3 6 (ι 3) (ι 6)) * ((1 : K))
                      ] : List K).sum),
            W (mkEdge (N := 8) (D := 3) 2 6 (ι 2) (ι 6)) * (([
                        W (mkEdge (N := 8) (D := 3) 3 4 (ι 3) (ι 4)) * ((1 : K))
                      ] : List K).sum)
          ] : List K).sum)
  ] : List K).sum)

end D19Round20
