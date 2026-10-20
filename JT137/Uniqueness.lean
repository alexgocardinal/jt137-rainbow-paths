import JT137.Chromatic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JT137

private theorem four_cases :
    ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
  decide

theorem forced_partition36 (c : Vertex → Fin 4)
    (h : Proper arc36 c) :
    c 1 = c 0 ∧ c 2 = c 0 ∧ c 3 = c 0 ∧ c 5 = c 4 ∧ c 6 = c 4 ∧ c 8 = c 7 ∧ c 9 = c 7 ∧ c 11 = c 10 ∧ c 12 = c 10 := by
  have edge0 : c 0 ≠ c 4 := h 0 4 (by decide)
  have edge1 : c 0 ≠ c 6 := h 0 6 (by decide)
  have edge2 : c 0 ≠ c 8 := h 0 8 (by decide)
  have edge3 : c 0 ≠ c 9 := h 0 9 (by decide)
  have edge4 : c 0 ≠ c 12 := h 0 12 (by decide)
  have edge5 : c 1 ≠ c 10 := h 1 10 (by decide)
  have edge6 : c 3 ≠ c 6 := h 3 6 (by decide)
  have edge7 : c 3 ≠ c 7 := h 3 7 (by decide)
  have edge8 : c 3 ≠ c 10 := h 3 10 (by decide)
  have edge9 : c 3 ≠ c 12 := h 3 12 (by decide)
  have edge10 : c 4 ≠ c 1 := h 4 1 (by decide)
  have edge11 : c 4 ≠ c 2 := h 4 2 (by decide)
  have edge12 : c 4 ≠ c 8 := h 4 8 (by decide)
  have edge13 : c 4 ≠ c 10 := h 4 10 (by decide)
  have edge14 : c 4 ≠ c 12 := h 4 12 (by decide)
  have edge15 : c 5 ≠ c 1 := h 5 1 (by decide)
  have edge16 : c 5 ≠ c 9 := h 5 9 (by decide)
  have edge17 : c 5 ≠ c 12 := h 5 12 (by decide)
  have edge18 : c 7 ≠ c 1 := h 7 1 (by decide)
  have edge19 : c 7 ≠ c 2 := h 7 2 (by decide)
  have edge20 : c 7 ≠ c 6 := h 7 6 (by decide)
  have edge21 : c 7 ≠ c 10 := h 7 10 (by decide)
  have edge22 : c 7 ≠ c 12 := h 7 12 (by decide)
  have edge23 : c 8 ≠ c 2 := h 8 2 (by decide)
  have edge24 : c 8 ≠ c 6 := h 8 6 (by decide)
  have edge25 : c 9 ≠ c 6 := h 9 6 (by decide)
  have edge26 : c 9 ≠ c 10 := h 9 10 (by decide)
  have edge27 : c 11 ≠ c 1 := h 11 1 (by decide)
  have edge28 : c 11 ≠ c 2 := h 11 2 (by decide)
  have edge29 : c 11 ≠ c 5 := h 11 5 (by decide)
  have edge30 : c 11 ≠ c 6 := h 11 6 (by decide)
  have edge31 : c 11 ≠ c 7 := h 11 7 (by decide)
  have edge32 : c 11 ≠ c 8 := h 11 8 (by decide)
  have edge33 : c 11 ≠ c 9 := h 11 9 (by decide)
  have edge34 : c 12 ≠ c 1 := h 12 1 (by decide)
  have edge35 : c 12 ≠ c 2 := h 12 2 (by decide)
  rcases four_cases (c 7) with h7 | h7 | h7 | h7
  ·
    rcases four_cases (c 11) with h11 | h11 | h11 | h11
    ·
      exact False.elim (edge31 (h11.trans h7.symm))
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
  ·
    rcases four_cases (c 11) with h11 | h11 | h11 | h11
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
    ·
      exact False.elim (edge31 (h11.trans h7.symm))
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
  ·
    rcases four_cases (c 11) with h11 | h11 | h11 | h11
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
    ·
      exact False.elim (edge31 (h11.trans h7.symm))
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
  ·
    rcases four_cases (c 11) with h11 | h11 | h11 | h11
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
    ·
      rcases four_cases (c 1) with h1 | h1 | h1 | h1
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
      ·
        rcases four_cases (c 12) with h12 | h12 | h12 | h12
        ·
          rcases four_cases (c 2) with h2 | h2 | h2 | h2
          ·
            exact False.elim (edge35 (h12.trans h2.symm))
          ·
            rcases four_cases (c 5) with h5 | h5 | h5 | h5
            ·
              exact False.elim (edge17 (h5.trans h12.symm))
            ·
              exact False.elim (edge15 (h5.trans h1.symm))
            ·
              exact False.elim (edge29 (h11.trans h5.symm))
            ·
              rcases four_cases (c 4) with h4 | h4 | h4 | h4
              ·
                exact False.elim (edge14 (h4.trans h12.symm))
              ·
                exact False.elim (edge10 (h4.trans h1.symm))
              ·
                rcases four_cases (c 10) with h10 | h10 | h10 | h10
                ·
                  rcases four_cases (c 9) with h9 | h9 | h9 | h9
                  ·
                    exact False.elim (edge26 (h9.trans h10.symm))
                  ·
                    rcases four_cases (c 6) with h6 | h6 | h6 | h6
                    ·
                      rcases four_cases (c 0) with h0 | h0 | h0 | h0
                      ·
                        exact False.elim (edge1 (h0.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge0 (h0.trans h4.symm))
                      ·
                        rcases four_cases (c 8) with h8 | h8 | h8 | h8
                        ·
                          exact False.elim (edge24 (h8.trans h6.symm))
                        ·
                          exact False.elim (edge23 (h8.trans h2.symm))
                        ·
                          exact False.elim (edge12 (h4.trans h8.symm))
                        ·
                          exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge30 (h11.trans h6.symm))
                    ·
                      exact False.elim (edge20 (h7.trans h6.symm))
                  ·
                    exact False.elim (edge33 (h11.trans h9.symm))
                  ·
                    exact False.elim (edge16 (h5.trans h9.symm))
                ·
                  exact False.elim (edge5 (h1.trans h10.symm))
                ·
                  exact False.elim (edge13 (h4.trans h10.symm))
                ·
                  exact False.elim (edge21 (h7.trans h10.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    exact False.elim (edge24 (h8.trans h6.symm))
                  ·
                    rcases four_cases (c 0) with h0 | h0 | h0 | h0
                    ·
                      exact False.elim (edge2 (h0.trans h8.symm))
                    ·
                      exact False.elim (edge1 (h0.trans h6.symm))
                    ·
                      rcases four_cases (c 9) with h9 | h9 | h9 | h9
                      ·
                        rcases four_cases (c 10) with h10 | h10 | h10 | h10
                        ·
                          exact False.elim (edge26 (h9.trans h10.symm))
                        ·
                          exact False.elim (edge5 (h1.trans h10.symm))
                        ·
                          rcases four_cases (c 3) with h3 | h3 | h3 | h3
                          ·
                            exact False.elim (edge9 (h3.trans h12.symm))
                          ·
                            exact False.elim (edge6 (h3.trans h6.symm))
                          ·
                            exact False.elim (edge8 (h3.trans h10.symm))
                          ·
                            exact False.elim (edge7 (h3.trans h7.symm))
                        ·
                          exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge25 (h9.trans h6.symm))
                      ·
                        exact False.elim (edge3 (h0.trans h9.symm))
                      ·
                        exact False.elim (edge16 (h5.trans h9.symm))
                    ·
                      exact False.elim (edge0 (h0.trans h4.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge23 (h8.trans h2.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
          ·
            exact False.elim (edge28 (h11.trans h2.symm))
          ·
            exact False.elim (edge19 (h7.trans h2.symm))
        ·
          exact False.elim (edge34 (h12.trans h1.symm))
        ·
          rcases four_cases (c 4) with h4 | h4 | h4 | h4
          ·
            rcases four_cases (c 2) with h2 | h2 | h2 | h2
            ·
              exact False.elim (edge11 (h4.trans h2.symm))
            ·
              rcases four_cases (c 8) with h8 | h8 | h8 | h8
              ·
                exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge23 (h8.trans h2.symm))
              ·
                exact False.elim (edge32 (h11.trans h8.symm))
              ·
                rcases four_cases (c 0) with h0 | h0 | h0 | h0
                ·
                  exact False.elim (edge0 (h0.trans h4.symm))
                ·
                  rcases four_cases (c 6) with h6 | h6 | h6 | h6
                  ·
                    rcases four_cases (c 9) with h9 | h9 | h9 | h9
                    ·
                      exact False.elim (edge25 (h9.trans h6.symm))
                    ·
                      exact False.elim (edge3 (h0.trans h9.symm))
                    ·
                      exact False.elim (edge33 (h11.trans h9.symm))
                    ·
                      rcases four_cases (c 10) with h10 | h10 | h10 | h10
                      ·
                        exact False.elim (edge13 (h4.trans h10.symm))
                      ·
                        exact False.elim (edge5 (h1.trans h10.symm))
                      ·
                        rcases four_cases (c 3) with h3 | h3 | h3 | h3
                        ·
                          exact False.elim (edge6 (h3.trans h6.symm))
                        ·
                          rcases four_cases (c 5) with h5 | h5 | h5 | h5
                          ·
                            exact ⟨(h1.trans h0.symm), (h2.trans h0.symm), (h3.trans h0.symm), (h5.trans h4.symm), (h6.trans h4.symm), (h8.trans h7.symm), (h9.trans h7.symm), (h11.trans h10.symm), (h12.trans h10.symm)⟩
                          ·
                            exact False.elim (edge15 (h5.trans h1.symm))
                          ·
                            exact False.elim (edge29 (h11.trans h5.symm))
                          ·
                            exact False.elim (edge16 (h5.trans h9.symm))
                        ·
                          exact False.elim (edge8 (h3.trans h10.symm))
                        ·
                          exact False.elim (edge7 (h3.trans h7.symm))
                      ·
                        exact False.elim (edge21 (h7.trans h10.symm))
                  ·
                    exact False.elim (edge1 (h0.trans h6.symm))
                  ·
                    exact False.elim (edge30 (h11.trans h6.symm))
                  ·
                    exact False.elim (edge20 (h7.trans h6.symm))
                ·
                  exact False.elim (edge4 (h0.trans h12.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
            ·
              exact False.elim (edge28 (h11.trans h2.symm))
            ·
              exact False.elim (edge19 (h7.trans h2.symm))
          ·
            exact False.elim (edge10 (h4.trans h1.symm))
          ·
            exact False.elim (edge14 (h4.trans h12.symm))
          ·
            rcases four_cases (c 6) with h6 | h6 | h6 | h6
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              rcases four_cases (c 0) with h0 | h0 | h0 | h0
              ·
                rcases four_cases (c 8) with h8 | h8 | h8 | h8
                ·
                  exact False.elim (edge2 (h0.trans h8.symm))
                ·
                  exact False.elim (edge24 (h8.trans h6.symm))
                ·
                  exact False.elim (edge32 (h11.trans h8.symm))
                ·
                  exact False.elim (edge12 (h4.trans h8.symm))
              ·
                exact False.elim (edge1 (h0.trans h6.symm))
              ·
                exact False.elim (edge4 (h0.trans h12.symm))
              ·
                exact False.elim (edge0 (h0.trans h4.symm))
            ·
              exact False.elim (edge30 (h11.trans h6.symm))
            ·
              exact False.elim (edge20 (h7.trans h6.symm))
        ·
          exact False.elim (edge22 (h7.trans h12.symm))
      ·
        exact False.elim (edge27 (h11.trans h1.symm))
      ·
        exact False.elim (edge18 (h7.trans h1.symm))
    ·
      exact False.elim (edge31 (h11.trans h7.symm))

end JT137
