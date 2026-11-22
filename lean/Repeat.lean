import Reduction
import Period2

/-!
# Rule 30: the left half is fixed by two columns, and a repetition bound

`left_det`: if two evolutions agree on columns 0 and -1 for `n` steps, their starting rows agree
at depths 1 to `n` on the left.

`repeat_bound`: let `x` be zero to the left of `-W` with a one at `-W`. If columns 0 and -1 read
the same for `n` steps starting at time `a` as they do starting at a later time `b`, then
`n < W + b`. (The left edge at time `b` is a one at depth `W + b`; the row at time `a` is zero there.)

`repeat_bound_alt`: the same for a center column that alternates 0,1,0,1,...: there column 0
repeats automatically and column -1 is 1 at odd times, so only column -1 at even times matters.

These do not prove that an alternating column is impossible.
-/

theorem rb_left (n l c r : Bool) (h : n = xor l (c || r)) : l = xor n (c || r) := by
  revert h; cases n <;> cases l <;> cases c <;> cases r <;> decide

/-- the left edge of any row that is zero left of `-W` and one at `-W` moves one cell per step -/
theorem left_edge_gen (x : Int → Bool) (W : Int) (hz : ∀ j, j < -W → x j = false) (hW : x (-W) = true) :
    ∀ t : Nat, (∀ j : Int, j < -W - (t : Int) → evo x t j = false) ∧ evo x t (-W - (t : Int)) = true := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun j hj => hz j (by omega), ?_⟩
    have e : -W - ((0 : Nat) : Int) = -W := by omega
    rw [e]; exact hW
  | succ t ih =>
    obtain ⟨ha, hb⟩ := ih
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [evo_succ, ha (j - 1) (by omega), ha j (by omega), ha (j + 1) (by omega)]; rfl
    · rw [evo_at x t (-W - ((t + 1 : Nat) : Int)) (-W - (t : Int) - 2) (-W - (t : Int)) (by omega) (by omega),
        ha (-W - (t : Int) - 2) (by omega), ha (-W - ((t + 1 : Nat) : Int)) (by omega), hb]; rfl

/-- columns 0 and -1 over `n` steps fix the starting row at depths 1 to `n` (and later rows less deep) -/
theorem left_det (x z : Int → Bool) (n : Nat)
    (h0 : ∀ t, t < n → evo x t 0 = evo z t 0)
    (h1 : ∀ t, t < n → evo x t (-1) = evo z t (-1)) :
    ∀ k : Nat,
      (∀ (t : Nat) (i : Int), i = -(k : Int) - 1 → t + k + 1 ≤ n → evo x t i = evo z t i) ∧
      (∀ (t : Nat) (i : Int), i = -(k : Int) - 2 → t + k + 2 ≤ n → evo x t i = evo z t i) := by
  have stepl : ∀ (i l r : Int) (t : Nat), i - 1 = l → i + 1 = r →
      evo x (t + 1) i = evo z (t + 1) i → evo x t i = evo z t i → evo x t r = evo z t r →
      evo x t l = evo z t l := by
    intro i l r t hl hr a b c
    have hx := rb_left _ _ _ _ (evo_at x t i l r hl hr)
    have hz := rb_left _ _ _ _ (evo_at z t i l r hl hr)
    rw [hx, hz, a, b, c]
  intro k
  induction k with
  | zero =>
    refine ⟨fun t i hi ht => ?_, fun t i hi ht => ?_⟩
    · have e : i = -1 := by omega
      rw [e]; exact h1 t (by omega)
    · exact stepl (-1) i 0 t (by omega) (by omega) (h1 (t + 1) (by omega)) (h1 t (by omega)) (h0 t (by omega))
  | succ k ih =>
    obtain ⟨p, q⟩ := ih
    refine ⟨fun t i hi ht => q t i (by omega) (by omega), fun t i hi ht => ?_⟩
    exact stepl (i + 1) i (i + 2) t (by omega) (by omega)
      (q (t + 1) (i + 1) (by omega) (by omega)) (q t (i + 1) (by omega) (by omega))
      (p t (i + 2) (by omega) (by omega))

/-- a stretch of columns 0 and -1 cannot be repeated too early -/
theorem repeat_bound (x : Int → Bool) (W : Int) (hz : ∀ j, j < -W → x j = false) (hW : x (-W) = true)
    (a b n : Nat) (hab : a < b) (hpos : 1 ≤ W + (b : Int))
    (h0 : ∀ t, t < n → evo x (a + t) 0 = evo x (b + t) 0)
    (h1 : ∀ t, t < n → evo x (a + t) (-1) = evo x (b + t) (-1)) :
    (n : Int) < W + (b : Int) := by
  apply Decidable.byContradiction
  intro hn
  have hD : ((W + (b : Int)).toNat : Int) = W + (b : Int) := by omega
  have det := left_det (evo x a) (evo x b) n
    (fun t ht => by rw [← evo_add, ← evo_add]; exact h0 t ht)
    (fun t ht => by rw [← evo_add, ← evo_add]; exact h1 t ht)
  have key : evo x a (-W - (b : Int)) = evo x b (-W - (b : Int)) :=
    (det ((W + (b : Int)).toNat - 1)).1 0 (-W - (b : Int)) (by omega) (by omega)
  have eb := (left_edge_gen x W hz hW b).2
  have ea := (left_edge_gen x W hz hW a).1 (-W - (b : Int)) (by omega)
  rw [ea, eb] at key
  exact Bool.noConfusion key

/-- the alternating case: only column -1 at even times has to repeat -/
theorem repeat_bound_alt (x : Int → Bool) (W : Int) (hz : ∀ j, j < -W → x j = false) (hW : x (-W) = true)
    (alt : ∀ t : Nat, evo x t 0 = decide (t % 2 = 1))
    (i i' m : Nat) (hii : i < i') (hpos : 1 ≤ W + 2 * (i' : Int))
    (he : ∀ s, s < m → evo x (2 * i + 2 * s) (-1) = evo x (2 * i' + 2 * s) (-1)) :
    2 * (m : Int) < W + 2 * (i' : Int) := by
  have odd : ∀ t : Nat, t % 2 = 1 → evo x t (-1) = true := by
    intro t ht
    have h := evo_at x t 0 (-1) 1 (by omega) (by omega)
    rw [alt (t + 1), alt t, decide_eq_false (by omega : ¬ (t + 1) % 2 = 1), decide_eq_true ht] at h
    exact p2_b _ _ h
  have r := repeat_bound x W hz hW (2 * i) (2 * i') (2 * m) (by omega) (by omega)
    (fun t _ => by
      rw [alt, alt]
      by_cases hp : (2 * i + t) % 2 = 1
      · rw [decide_eq_true hp, decide_eq_true (by omega : (2 * i' + t) % 2 = 1)]
      · rw [decide_eq_false hp, decide_eq_false (by omega : ¬ (2 * i' + t) % 2 = 1)])
    (fun t ht => by
      rcases Nat.mod_two_eq_zero_or_one t with h | h
      · have q := he (t / 2) (by omega)
        rw [(by omega : 2 * i + 2 * (t / 2) = 2 * i + t), (by omega : 2 * i' + 2 * (t / 2) = 2 * i' + t)] at q
        exact q
      · rw [odd (2 * i + t) (by omega), odd (2 * i' + t) (by omega)])
  omega

#print axioms repeat_bound_alt

/-- For a row with a leftmost one, columns 0 and -1 are never both eventually periodic with a
common period (and so never both eventually periodic at all: take a common multiple).
For Rule 30 this is the two-adjacent-columns theorem of Jen and Kopra, here with the explicit
bound of `repeat_bound` behind it. -/
theorem two_columns_never_periodic (x : Int → Bool) (W : Int)
    (hz : ∀ j, j < -W → x j = false) (hW : x (-W) = true) (t0 p : Nat) (hp : 0 < p)
    (h0 : ∀ t, t0 ≤ t → evo x (t + p) 0 = evo x t 0)
    (h1 : ∀ t, t0 ≤ t → evo x (t + p) (-1) = evo x t (-1)) : False := by
  have r := repeat_bound x W hz hW (t0 + W.natAbs) (t0 + W.natAbs + p)
    ((W + ((t0 + W.natAbs + p : Nat) : Int)).toNat) (by omega) (by omega)
    (fun t _ => by
      rw [(by omega : t0 + W.natAbs + p + t = t0 + W.natAbs + t + p)]
      exact (h0 _ (by omega)).symm)
    (fun t _ => by
      rw [(by omega : t0 + W.natAbs + p + t = t0 + W.natAbs + t + p)]
      exact (h1 _ (by omega)).symm)
  omega

/-- the single-cell pattern: its center column and the column to its left are never both
eventually periodic with a common period -/
theorem seed0_two_columns (t0 p : Nat) (hp : 0 < p)
    (h0 : ∀ t, t0 ≤ t → evo seed0 (t + p) 0 = evo seed0 t 0)
    (h1 : ∀ t, t0 ≤ t → evo seed0 (t + p) (-1) = evo seed0 t (-1)) : False :=
  two_columns_never_periodic seed0 0 (fun j hj => by simp [seed0]; omega) (by decide) t0 p hp h0 h1

#print axioms seed0_two_columns

/-- If the center column of a row with a leftmost one alternates 0,1,0,1,... forever, then
column -1 read at even times is not eventually periodic. -/
theorem alt_e_never_periodic (x : Int → Bool) (W : Int)
    (hz : ∀ j, j < -W → x j = false) (hW : x (-W) = true)
    (alt : ∀ t : Nat, evo x t 0 = decide (t % 2 = 1))
    (s0 q : Nat) (hq : 0 < q)
    (he : ∀ s, s0 ≤ s → evo x (2 * (s + q)) (-1) = evo x (2 * s) (-1)) : False := by
  have odd : ∀ t : Nat, t % 2 = 1 → evo x t (-1) = true := by
    intro t ht
    have h := evo_at x t 0 (-1) 1 (by omega) (by omega)
    rw [alt (t + 1), alt t, decide_eq_false (by omega : ¬ (t + 1) % 2 = 1), decide_eq_true ht] at h
    exact p2_b _ _ h
  refine two_columns_never_periodic x W hz hW (2 * s0) (2 * q) (by omega) (fun t _ => ?_) (fun t ht => ?_)
  · rw [alt, alt]
    by_cases hp : t % 2 = 1
    · rw [decide_eq_true hp, decide_eq_true (by omega : (t + 2 * q) % 2 = 1)]
    · rw [decide_eq_false hp, decide_eq_false (by omega : ¬ (t + 2 * q) % 2 = 1)]
  · rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have r := he (t / 2) (by omega)
      rw [(by omega : 2 * (t / 2 + q) = t + 2 * q), (by omega : 2 * (t / 2) = t)] at r
      exact r
    · rw [odd (t + 2 * q) (by omega), odd t h]

#print axioms alt_e_never_periodic
