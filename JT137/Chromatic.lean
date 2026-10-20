import JT137.Coloring
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JT137

theorem no_three_coloring36 (c : Vertex → Fin 3)
    (h : Proper arc36 c) : False := by
  have bound0 := (c 0).isLt
  have bound1 := (c 1).isLt
  have bound2 := (c 2).isLt
  have bound3 := (c 3).isLt
  have bound4 := (c 4).isLt
  have bound5 := (c 5).isLt
  have bound6 := (c 6).isLt
  have bound7 := (c 7).isLt
  have bound8 := (c 8).isLt
  have bound9 := (c 9).isLt
  have bound10 := (c 10).isLt
  have bound11 := (c 11).isLt
  have bound12 := (c 12).isLt
  have edge0 : (c 0).val ≠ (c 4).val := by
    intro he
    exact (h 0 4 (by decide)) (Fin.ext he)
  have edge1 : (c 0).val ≠ (c 6).val := by
    intro he
    exact (h 0 6 (by decide)) (Fin.ext he)
  have edge2 : (c 0).val ≠ (c 8).val := by
    intro he
    exact (h 0 8 (by decide)) (Fin.ext he)
  have edge3 : (c 0).val ≠ (c 9).val := by
    intro he
    exact (h 0 9 (by decide)) (Fin.ext he)
  have edge4 : (c 0).val ≠ (c 12).val := by
    intro he
    exact (h 0 12 (by decide)) (Fin.ext he)
  have edge5 : (c 1).val ≠ (c 10).val := by
    intro he
    exact (h 1 10 (by decide)) (Fin.ext he)
  have edge6 : (c 3).val ≠ (c 6).val := by
    intro he
    exact (h 3 6 (by decide)) (Fin.ext he)
  have edge7 : (c 3).val ≠ (c 7).val := by
    intro he
    exact (h 3 7 (by decide)) (Fin.ext he)
  have edge8 : (c 3).val ≠ (c 10).val := by
    intro he
    exact (h 3 10 (by decide)) (Fin.ext he)
  have edge9 : (c 3).val ≠ (c 12).val := by
    intro he
    exact (h 3 12 (by decide)) (Fin.ext he)
  have edge10 : (c 4).val ≠ (c 1).val := by
    intro he
    exact (h 4 1 (by decide)) (Fin.ext he)
  have edge11 : (c 4).val ≠ (c 2).val := by
    intro he
    exact (h 4 2 (by decide)) (Fin.ext he)
  have edge12 : (c 4).val ≠ (c 8).val := by
    intro he
    exact (h 4 8 (by decide)) (Fin.ext he)
  have edge13 : (c 4).val ≠ (c 10).val := by
    intro he
    exact (h 4 10 (by decide)) (Fin.ext he)
  have edge14 : (c 4).val ≠ (c 12).val := by
    intro he
    exact (h 4 12 (by decide)) (Fin.ext he)
  have edge15 : (c 5).val ≠ (c 1).val := by
    intro he
    exact (h 5 1 (by decide)) (Fin.ext he)
  have edge16 : (c 5).val ≠ (c 9).val := by
    intro he
    exact (h 5 9 (by decide)) (Fin.ext he)
  have edge17 : (c 5).val ≠ (c 12).val := by
    intro he
    exact (h 5 12 (by decide)) (Fin.ext he)
  have edge18 : (c 7).val ≠ (c 1).val := by
    intro he
    exact (h 7 1 (by decide)) (Fin.ext he)
  have edge19 : (c 7).val ≠ (c 2).val := by
    intro he
    exact (h 7 2 (by decide)) (Fin.ext he)
  have edge20 : (c 7).val ≠ (c 6).val := by
    intro he
    exact (h 7 6 (by decide)) (Fin.ext he)
  have edge21 : (c 7).val ≠ (c 10).val := by
    intro he
    exact (h 7 10 (by decide)) (Fin.ext he)
  have edge22 : (c 7).val ≠ (c 12).val := by
    intro he
    exact (h 7 12 (by decide)) (Fin.ext he)
  have edge23 : (c 8).val ≠ (c 2).val := by
    intro he
    exact (h 8 2 (by decide)) (Fin.ext he)
  have edge24 : (c 8).val ≠ (c 6).val := by
    intro he
    exact (h 8 6 (by decide)) (Fin.ext he)
  have edge25 : (c 9).val ≠ (c 6).val := by
    intro he
    exact (h 9 6 (by decide)) (Fin.ext he)
  have edge26 : (c 9).val ≠ (c 10).val := by
    intro he
    exact (h 9 10 (by decide)) (Fin.ext he)
  have edge27 : (c 11).val ≠ (c 1).val := by
    intro he
    exact (h 11 1 (by decide)) (Fin.ext he)
  have edge28 : (c 11).val ≠ (c 2).val := by
    intro he
    exact (h 11 2 (by decide)) (Fin.ext he)
  have edge29 : (c 11).val ≠ (c 5).val := by
    intro he
    exact (h 11 5 (by decide)) (Fin.ext he)
  have edge30 : (c 11).val ≠ (c 6).val := by
    intro he
    exact (h 11 6 (by decide)) (Fin.ext he)
  have edge31 : (c 11).val ≠ (c 7).val := by
    intro he
    exact (h 11 7 (by decide)) (Fin.ext he)
  have edge32 : (c 11).val ≠ (c 8).val := by
    intro he
    exact (h 11 8 (by decide)) (Fin.ext he)
  have edge33 : (c 11).val ≠ (c 9).val := by
    intro he
    exact (h 11 9 (by decide)) (Fin.ext he)
  have edge34 : (c 12).val ≠ (c 1).val := by
    intro he
    exact (h 12 1 (by decide)) (Fin.ext he)
  have edge35 : (c 12).val ≠ (c 2).val := by
    intro he
    exact (h 12 2 (by decide)) (Fin.ext he)
  omega

theorem arc36_implies37 :
    ∀ u v : Vertex, arc36 u v = true → arc37 u v = true := by
  decide

theorem no_three_coloring37 (c : Vertex → Fin 3)
    (h : Proper arc37 c) : False := by
  apply no_three_coloring36 c
  intro u v huv
  exact h u v (arc36_implies37 u v huv)

end JT137
