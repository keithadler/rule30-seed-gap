/-!
Rule 30, constant center column.

A configuration is `x : Int → Bool` (true = black). One step is `x'(i) = x(i-1) xor (x(i) or x(i+1))`.
Theorem `no_const_column`: if a nonzero configuration has support inside `[-A, A]`, then its center
column cannot be constant on the times `0 .. A+2`.  This is sharp (a SAT search finds the first impossible horizon is exactly A+2).
It says nothing about the eventual periodicity of the single-cell pattern (Wolfram's Problem 1); it is the period-1 case
for finite seeds only.
-/

def step (x : Int → Bool) (i : Int) : Bool := xor (x (i - 1)) (x i || x (i + 1))

def evo (x : Int → Bool) : Nat → Int → Bool
  | 0 => x
  | t + 1 => step (evo x t)

theorem evo_succ (x : Int → Bool) (t : Nat) (i : Int) :
    evo x (t + 1) i = xor (evo x t (i - 1)) (evo x t i || evo x t (i + 1)) := rfl

/-! Boolean helper facts, stated on plain `Bool`s so that `simp` never sees `evo`. -/
theorem b_true (a b : Bool) (h : true = xor a (true || b)) : a = false := by
  cases a <;> cases b <;> simp_all
theorem b_par (p v : Bool) (h : (!p) = xor v ((!p) || p)) : v = p := by
  cases p <;> cases v <;> simp_all
theorem b_y1 (a b : Bool) (h : false = xor a (false || b)) : a = b := by
  cases a <;> cases b <;> simp_all

/-! ### Constant 1 -/

theorem left_true (x : Int → Bool) (T : Nat) (hc : ∀ t, t ≤ T → evo x t 0 = true) :
    ∀ k : Nat,
      (∀ t, t + k ≤ T → evo x t (-(k : Int)) = decide (k % 2 = 0)) ∧
      (∀ t, t + (k + 1) ≤ T → evo x t (-((k + 1 : Nat) : Int)) = decide ((k + 1) % 2 = 0)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have e0 : (-((0 : Nat) : Int)) = 0 := by omega
      rw [e0, hc t (by omega)]; rfl
    · have h := evo_succ x t 0
      rw [hc (t + 1) (by omega), hc t (by omega)] at h
      have e1 : (0 : Int) - 1 = -((0 + 1 : Nat) : Int) := by omega
      rw [e1] at h
      have := b_true _ _ h
      rw [this]; rfl
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun t ht => ih2 t (by omega), fun t ht => ?_⟩
    have h := evo_succ x t (-((k + 1 : Nat) : Int))
    have e1 : -((k + 1 : Nat) : Int) - 1 = -((k + 1 + 1 : Nat) : Int) := by omega
    have e2 : -((k + 1 : Nat) : Int) + 1 = -(k : Int) := by omega
    rw [e1, e2, ih2 (t + 1) (by omega), ih2 t (by omega), ih1 t (by omega)] at h
    have f1 : decide ((k + 1) % 2 = 0) = !decide (k % 2 = 0) := by
      by_cases hk : k % 2 = 0
      · have : ¬ ((k + 1) % 2 = 0) := by omega
        simp [hk, this]
      · have : (k + 1) % 2 = 0 := by omega
        simp [hk, this]
    have f2 : decide ((k + 1 + 1) % 2 = 0) = decide (k % 2 = 0) := by
      have : (k + 1 + 1) % 2 = k % 2 := by omega
      rw [this]
    rw [f1] at h
    rw [f2]
    exact (b_par _ _ h.symm.symm).symm.symm

/-! ### Constant 0 -/

/-- the right neighbor column -/
abbrev s (x : Int → Bool) (t : Nat) : Bool := evo x t 1
/-- the left columns -/
abbrev y (x : Int → Bool) (k t : Nat) : Bool := evo x t (-(k : Int))

theorem yrule (x : Int → Bool) (k t : Nat) :
    y x (k + 2) t = xor (y x (k + 1) (t + 1)) (y x (k + 1) t || y x k t) := by
  have e := evo_succ x t (-((k + 1 : Nat) : Int))
  have e1 : -((k + 1 : Nat) : Int) - 1 = -((k + 2 : Nat) : Int) := by omega
  have e2 : -((k + 1 : Nat) : Int) + 1 = -(k : Int) := by omega
  rw [e1, e2] at e
  simp only [y]
  generalize evo x t (-((k + 2 : Nat) : Int)) = a at *
  generalize evo x t (-((k + 1 : Nat) : Int)) = b at *
  generalize evo x t (-(k : Int)) = d at *
  generalize evo x (t + 1) (-((k + 1 : Nat) : Int)) = f at *
  cases a <;> cases b <;> cases d <;> cases f <;> simp_all

section ConstZero
variable (x : Int → Bool) (T : Nat) (hc : ∀ t, t ≤ T → evo x t 0 = false)
include hc

theorem mono (t : Nat) (ht : t + 1 ≤ T) : s x t = true → s x (t + 1) = true := by
  intro h
  have e := evo_succ x t 1
  have e0 : (1 : Int) - 1 = 0 := by omega
  rw [e0, hc t (by omega)] at e
  simp only [s] at h ⊢
  rw [e, h]; simp

theorem y1 (t : Nat) (ht : t + 1 ≤ T) : y x 1 t = s x t := by
  have e := evo_succ x t 0
  rw [hc (t + 1) (by omega), hc t (by omega)] at e
  have e1 : (0 : Int) - 1 = -((1 : Nat) : Int) := by omega
  have e2 : (0 : Int) + 1 = 1 := by omega
  rw [e1, e2] at e
  exact b_y1 _ _ e

theorem y2 (t : Nat) (ht : t + 2 ≤ T) : y x 2 t = xor (s x (t + 1)) (s x t) := by
  have r := yrule x 0 t
  have h0 : y x 0 t = false := by
    have e0 : (-((0 : Nat) : Int)) = 0 := by omega
    simp only [y]; rw [e0, hc t (by omega)]
  have a := y1 x T hc (t + 1) (by omega)
  have b := y1 x T hc t (by omega)
  rw [h0] at r
  simp only [Nat.zero_add] at r
  rw [a, b] at r
  simpa using r


theorem D (k : Nat) : 1 ≤ k → ∀ t, t + k + 2 ≤ T → y x (k + 2) t = y x k (t + 2) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk t ht
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | h3
    · have r : y x 3 t = xor (y x 2 (t + 1)) (y x 2 t || y x 1 t) := yrule x 1 t
      have a : y x 2 (t + 1) = xor (s x (t + 2)) (s x (t + 1)) := y2 x T hc (t + 1) (by omega)
      have b : y x 2 t = xor (s x (t + 1)) (s x t) := y2 x T hc t (by omega)
      have c : y x 1 t = s x t := y1 x T hc t (by omega)
      have d : y x 1 (t + 2) = s x (t + 2) := y1 x T hc (t + 2) (by omega)
      have m0 := mono x T hc t (by omega)
      have m1 : s x (t + 1) = true → s x (t + 2) = true := mono x T hc (t + 1) (by omega)
      show y x 3 t = y x 1 (t + 2)
      rw [r, a, b, c, d]
      generalize s x t = p at *
      generalize s x (t + 1) = q at *
      generalize s x (t + 2) = u at *
      cases p <;> cases q <;> cases u <;> simp_all
    · have r : y x 4 t = xor (y x 3 (t + 1)) (y x 3 t || y x 2 t) := yrule x 2 t
      have a : y x 3 (t + 1) = y x 1 (t + 1 + 2) := ih 1 (by omega) (by omega) (t + 1) (by omega)
      have b : y x 3 t = y x 1 (t + 2) := ih 1 (by omega) (by omega) t (by omega)
      have c : y x 1 (t + 1 + 2) = s x (t + 3) := y1 x T hc (t + 1 + 2) (by omega)
      have d : y x 1 (t + 2) = s x (t + 2) := y1 x T hc (t + 2) (by omega)
      have e : y x 2 t = xor (s x (t + 1)) (s x t) := y2 x T hc t (by omega)
      have f : y x 2 (t + 2) = xor (s x (t + 3)) (s x (t + 2)) := y2 x T hc (t + 2) (by omega)
      have m0 := mono x T hc t (by omega)
      have m1 : s x (t + 1) = true → s x (t + 2) = true := mono x T hc (t + 1) (by omega)
      show y x 4 t = y x 2 (t + 2)
      rw [r, a, b, c, d, e, f]
      generalize s x t = p at *
      generalize s x (t + 1) = q at *
      generalize s x (t + 2) = u at *
      generalize s x (t + 3) = v at *
      cases p <;> cases q <;> cases u <;> cases v <;> simp_all
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      have L := yrule x (m + 3) t
      have R : y x (m + 3) (t + 2) = xor (y x (m + 2) (t + 3)) (y x (m + 2) (t + 2) || y x (m + 1) (t + 2)) :=
        yrule x (m + 1) (t + 2)
      have ha : y x (m + 3 + 1) (t + 1) = y x (m + 2) (t + 3) :=
        ih (m + 2) (by omega) (by omega) (t + 1) (by omega)
      have hb : y x (m + 3 + 1) t = y x (m + 2) (t + 2) :=
        ih (m + 2) (by omega) (by omega) t (by omega)
      have hc' : y x (m + 3) t = y x (m + 1) (t + 2) :=
        ih (m + 1) (by omega) (by omega) t (by omega)
      rw [L, R, ha, hb, hc']

theorem E (i k t : Nat) (hk : 1 ≤ k) (ht : t + 2 * i + k ≤ T) : y x (k + 2 * i) t = y x k (t + 2 * i) := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
    have e1 : k + 2 * (i + 1) = (k + 2 * i) + 2 := by omega
    have e2 : t + 2 * (i + 1) = (t + 2) + 2 * i := by omega
    rw [e1, e2, D x T hc (k + 2 * i) (by omega) t (by omega)]
    exact ih (t + 2) (by omega)

theorem hodd (j : Nat) (hj : 2 * j + 1 ≤ T) : y x (2 * j + 1) 0 = s x (2 * j) := by
  have := E x T hc j 1 0 (by omega) (by omega)
  have e : 2 * j + 1 = 1 + 2 * j := by omega
  rw [e, this, Nat.zero_add]
  exact y1 x T hc (2 * j) (by omega)

theorem heven (j : Nat) (hj : 2 * j + 2 ≤ T) :
    y x (2 * j + 2) 0 = xor (s x (2 * j + 1)) (s x (2 * j)) := by
  have := E x T hc j 2 0 (by omega) (by omega)
  have e : 2 * j + 2 = 2 + 2 * j := by omega
  rw [e, this, Nat.zero_add]
  exact y2 x T hc (2 * j) (by omega)

end ConstZero

theorem b_z1 (v : Bool) (h : false = xor false (false || v)) : v = false := by
  cases v <;> simp_all

theorem par (n : Nat) : (∃ j, n = 2 * j) ∨ (∃ j, n = 2 * j + 1) := by
  by_cases h : n % 2 = 0
  · exact Or.inl ⟨n / 2, by omega⟩
  · exact Or.inr ⟨n / 2, by omega⟩

theorem zero_case (x : Int → Bool) (A : Nat)
    (hz : ∀ i : Int, i < -(A : Int) ∨ (A : Int) < i → x i = false)
    (hne : ∃ i, x i = true) (hc : ∀ t, t ≤ A + 2 → evo x t 0 = false) : False := by
  have hy0 : ∀ k : Nat, A < k → y x k 0 = false := fun k hk => hz _ (Or.inl (by omega))
  -- s A = false
  have hsA : s x A = false := by
    rcases par A with ⟨j, hj⟩ | ⟨j, hj⟩
    · have h1 := hodd x (A + 2) hc j (by omega)
      have h2 := hy0 (2 * j + 1) (by omega)
      rw [h2] at h1
      rw [hj]; exact h1.symm
    · have h1 := hodd x (A + 2) hc (j + 1) (by omega)
      have h2 := hy0 (2 * (j + 1) + 1) (by omega)
      rw [h2] at h1
      have h3 : s x (A + 1) = false := by
        have : A + 1 = 2 * (j + 1) := by omega
        rw [this]; exact h1.symm
      refine Classical.byContradiction fun hA => ?_
      have hA' : s x A = true := by simpa using hA
      have := mono x (A + 2) hc A (by omega) hA'
      rw [h3] at this; exact absurd this (by simp)
  have hs : ∀ t, t ≤ A → s x t = false := by
    intro t ht
    refine Classical.byContradiction fun hne' => ?_
    have ht' : s x t = true := by simpa using hne'
    have up : ∀ d, t + d ≤ A → s x (t + d) = true := by
      intro d
      induction d with
      | zero => intro _; simpa using ht'
      | succ d ih =>
        intro hd
        exact mono x (A + 2) hc (t + d) (by omega) (ih (by omega))
    have := up (A - t) (by omega)
    rw [show t + (A - t) = A by omega, hsA] at this
    exact absurd this (by simp)
  -- left side of the seed is zero
  have hleft : ∀ k : Nat, 1 ≤ k → k ≤ A → y x k 0 = false := by
    intro k hk1 hk2
    rcases par k with ⟨j, hj⟩ | ⟨j, hj⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj2 : k = 2 * j' + 2 := by omega
      rw [hj2, heven x (A + 2) hc j' (by omega), hs _ (by omega), hs _ (by omega)]; rfl
    · rw [hj, hodd x (A + 2) hc j (by omega)]; exact hs _ (by omega)
  -- right side of the seed is zero
  have hR1 : ∀ t, t + 1 ≤ A + 1 → evo x t 1 = false := fun t ht => hs t (by omega)
  have hR2 : ∀ t, t + 2 ≤ A + 1 → evo x t 2 = false := by
    intro t ht
    have e := evo_succ x t 1
    have e0 : (1 : Int) - 1 = 0 := by omega
    have e2 : (1 : Int) + 1 = 2 := by omega
    rw [e0, e2, hc t (by omega)] at e
    have a : evo x (t + 1) 1 = false := hs (t + 1) (by omega)
    have b : evo x t 1 = false := hs t (by omega)
    rw [a, b] at e
    exact b_z1 _ e
  have hRz : ∀ j : Nat,
      (∀ t, t + (j + 1) ≤ A + 1 → evo x t ((j + 1 : Nat) : Int) = false) ∧
      (∀ t, t + (j + 2) ≤ A + 1 → evo x t ((j + 2 : Nat) : Int) = false) := by
    intro j
    induction j with
    | zero => exact ⟨fun t ht => by simpa using hR1 t (by omega), fun t ht => by simpa using hR2 t (by omega)⟩
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨fun t ht => ih2 t (by omega), fun t ht => ?_⟩
      have e := evo_succ x t ((j + 2 : Nat) : Int)
      have e1 : ((j + 2 : Nat) : Int) - 1 = ((j + 1 : Nat) : Int) := by omega
      have e2 : ((j + 2 : Nat) : Int) + 1 = ((j + 1 + 2 : Nat) : Int) := by omega
      rw [e1, e2, ih2 (t + 1) (by omega), ih1 t (by omega), ih2 t (by omega)] at e
      exact b_z1 _ e
  -- the whole seed is zero, contradicting `hne`
  obtain ⟨i, hi⟩ := hne
  have : x i = false := by
    rcases (by omega : (i < -(A : Int) ∨ (A : Int) < i) ∨ i = 0 ∨ (1 ≤ i ∧ i ≤ A) ∨ (i ≤ -1 ∧ -(A : Int) ≤ i))
      with h | h | h | h
    · exact hz i h
    · rw [h]; exact hc 0 (by omega)
    · obtain ⟨n, hn⟩ : ∃ n : Nat, i = (n : Int) := ⟨i.toNat, by omega⟩
      obtain ⟨m, hm⟩ : ∃ m : Nat, n = m + 1 := ⟨n - 1, by omega⟩
      subst hn; subst hm
      exact (hRz m).1 0 (by omega)
    · obtain ⟨n, hn⟩ : ∃ n : Nat, i = -(n : Int) := ⟨(-i).toNat, by omega⟩
      subst hn
      have := hleft n (by omega) (by omega)
      exact this
  rw [this] at hi; exact absurd hi (by simp)

/-- Main theorem: a nonzero seed supported in `[-A, A]` cannot have a constant center column on times `0 .. A+2`. -/
theorem no_const_column (x : Int → Bool) (A : Nat)
    (hz : ∀ i : Int, i < -(A : Int) ∨ (A : Int) < i → x i = false)
    (hne : ∃ i, x i = true) (c : Bool) (hc : ∀ t, t ≤ A + 2 → evo x t 0 = c) : False := by
  cases c with
  | false => exact zero_case x A hz hne hc
  | true =>
    obtain ⟨h1, h2⟩ := left_true x (A + 2) hc (A + 1)
    have a := h1 0 (by omega)
    have b := h2 0 (by omega)
    have za : x (-((A + 1 : Nat) : Int)) = false := hz _ (Or.inl (by omega))
    have zb : x (-((A + 1 + 1 : Nat) : Int)) = false := hz _ (Or.inl (by omega))
    change x _ = _ at a
    change x _ = _ at b
    rw [za] at a; rw [zb] at b
    rcases (by omega : (A + 1) % 2 = 0 ∨ (A + 1 + 1) % 2 = 0) with h | h
    · rw [decide_eq_true h] at a; exact absurd a (by simp)
    · rw [decide_eq_true h] at b; exact absurd b (by simp)

#print axioms no_const_column

/-! ### Sanity checks (the definitions are really Rule 30, and the bound is sharp for A = 0) -/

def seed0 : Int → Bool := fun i => decide (i = 0)

/-- center column of the single-cell pattern: 1 1 0 1 1 1 0 0, the known Rule 30 sequence -/
example : (List.range 8).map (fun t => evo seed0 t 0) = [true, true, false, true, true, true, false, false] := by decide

/-- sharpness for A = 0: the single cell has a constant center column on times 0..1 but not 0..2 -/
example : (∀ t, t ≤ 1 → evo seed0 t 0 = true) ∧ evo seed0 2 0 = false := by
  refine ⟨fun t ht => ?_, by decide⟩
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;> decide
