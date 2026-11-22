import ConstColumn

/-!
Rule 30, alternating center column: cells it forces on the left.

If the center column reads `0,1,0,1,0` on five consecutive times `t .. t+4`, then, writing `y` for column 1,
* column -1 is `!y` at time `t`, and `1` at time `t+1`,
* column -2 is `y(t)` at time `t` and `y(t+2)` at times `t+1`, `t+2`,
* column -3 is `!y(t+2)` at times `t` and `t+1`,
* column -4 is `0` at time `t`   (`alt_forces_col4`).
The last one uses the right side: `y(t) = 1` forces `y(t+2) = 0`.
This is a structural lemma only. It does not prove that an alternating column is impossible.
-/

theorem evo_at (x : Int → Bool) (t : Nat) (i l r : Int) (hl : i - 1 = l) (hr : i + 1 = r) :
    evo x (t + 1) i = xor (evo x t l) (evo x t i || evo x t r) := by
  subst hl; subst hr; rfl

theorem p2_a (m y : Bool) (h : true = xor m (false || y)) : m = !y := by
  cases m <;> cases y <;> simp_all
theorem p2_b (m y : Bool) (h : false = xor m (true || y)) : m = true := by
  cases m <;> cases y <;> simp_all
theorem p2_c (y0 z0 y1 z1 y2 : Bool) (h5 : y1 = xor false (y0 || z0)) (h6 : y2 = xor true (y1 || z1)) :
    y0 = true → y2 = false := by
  revert h5 h6
  cases y0 <;> cases z0 <;> cases y1 <;> cases z1 <;> cases y2 <;> decide
theorem p2_d (m y : Bool) (h : true = xor m ((!y) || false)) : m = y := by
  cases m <;> cases y <;> simp_all
theorem p2_e (m y : Bool) (h : (!y) = xor m (true || true)) : m = y := by
  cases m <;> cases y <;> simp_all
theorem p2_f (m y0 y2 : Bool) (h : y2 = xor m (y0 || !y0)) : m = !y2 := by
  cases m <;> cases y0 <;> cases y2 <;> simp_all
theorem p2_g (m y2 : Bool) (h : y2 = xor m (y2 || true)) : m = !y2 := by
  cases m <;> cases y2 <;> simp_all
theorem p2_h (m y0 y2 : Bool) (hy : y0 = true → y2 = false) (h : (!y2) = xor m ((!y2) || y0)) : m = false := by
  cases m <;> cases y0 <;> cases y2 <;> simp_all

/-- Center column `0,1,0,1,0` on times `t .. t+4` forces column -4 to be 0 at time `t`. -/
theorem alt_forces_col4 (x : Int → Bool) (t : Nat)
    (c0 : evo x t 0 = false) (c1 : evo x (t + 1) 0 = true) (c2 : evo x (t + 2) 0 = false)
    (c3 : evo x (t + 3) 0 = true) (c4 : evo x (t + 4) 0 = false) :
    evo x t (-4) = false := by
  have E1 := evo_at x t 0 (-1) 1 rfl rfl
  have E2 := evo_at x (t + 1) 0 (-1) 1 rfl rfl
  have E3 := evo_at x (t + 2) 0 (-1) 1 rfl rfl
  have E4 := evo_at x (t + 3) 0 (-1) 1 rfl rfl
  have E5 := evo_at x t 1 0 2 rfl rfl
  have E6 := evo_at x (t + 1) 1 0 2 rfl rfl
  have E7 := evo_at x t (-1) (-2) 0 rfl rfl
  have E8 := evo_at x (t + 1) (-1) (-2) 0 rfl rfl
  have E9 := evo_at x (t + 2) (-1) (-2) 0 rfl rfl
  have E10 := evo_at x t (-2) (-3) (-1) rfl rfl
  have E11 := evo_at x (t + 1) (-2) (-3) (-1) rfl rfl
  have E12 := evo_at x t (-3) (-4) (-2) rfl rfl
  rw [c1, c0] at E1; rw [c2, c1] at E2; rw [c3, c2] at E3; rw [c4, c3] at E4
  rw [c0] at E5; rw [c1] at E6
  have m10 := p2_a _ _ E1
  have m11 := p2_b _ _ E2
  have m12 := p2_a _ _ E3
  have m13 := p2_b _ _ E4
  have hy := p2_c _ _ _ _ _ E5 E6
  rw [m11, m10, c0] at E7
  have m20 := p2_d _ _ E7
  rw [m12, m11, c1] at E8
  have m21 := p2_e _ _ E8
  rw [m13, m12, c2] at E9
  have m22 := p2_d _ _ E9
  rw [m21, m20, m10] at E10
  have m30 := p2_f _ _ _ E10
  rw [m22, m21, m11] at E11
  have m31 := p2_g _ _ E11
  rw [m31, m30, m20] at E12
  exact p2_h _ _ _ hy E12

#print axioms alt_forces_col4
