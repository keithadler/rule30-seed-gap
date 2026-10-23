import ConstColumn

/-!
How the finite-gap conjecture would give Wolfram's Rule 30 Prize Problem 1 (center column eventually periodic?).

Everything here is a formal REDUCTION. Nothing in this file proves `GapLemma` (it is open; numerical evidence only), except the period-1 case, which is `no_const_column`.

* `Problem1NonPeriodic`: the center column of the single-cell pattern is not eventually periodic.
* `FiniteNeverPeriodic`: no nonzero finite configuration has a center column that is periodic from time 0.
* `UniformGapLemma`: for each period p there is ONE G such that no nonzero finite seed of radius r has a p-periodic center column on times 0 .. r + G, for every r.

IMPORTANT (correction, 2026-10-23): the measured gap grows slowly with r (about 9 for r = 29..37, 12-13 at r = 55..56, roughly 2*log2 r), so `UniformGapLemma` is probably FALSE as stated.
The statement the evidence actually supports is weaker: every finite seed eventually deviates from every periodic center column (`FiniteNeverPeriodic`, which is exactly the open question of Condrey and Kopra),
quantitatively with gap at most about C*log2(r). Only `FiniteNeverPeriodic` is needed for Problem 1; the theorems below are sound reductions either way.
-/

def Fin' (x : Int → Bool) : Prop := ∃ B : Nat, ∀ i : Int, B < i.natAbs → x i = false

/-- trace of the configuration after `a` steps, followed for `b` steps, is the trace of the original after `a + b` steps -/
theorem evo_add (x : Int → Bool) (a b : Nat) : evo x (a + b) = evo (evo x a) b := by
  induction b with
  | zero => rfl
  | succ b ih => show step (evo x (a + b)) = step (evo (evo x a) b); rw [ih]

/-- support grows by at most one cell per side per step -/
theorem support_grows (x : Int → Bool) (B : Nat) (h : ∀ i : Int, B < i.natAbs → x i = false) :
    ∀ t : Nat, ∀ i : Int, B + t < i.natAbs → evo x t i = false := by
  intro t
  induction t with
  | zero => intro i hi; exact h i (by simpa using hi)
  | succ t ih =>
    intro i hi
    rw [evo_succ]
    have a : evo x t (i - 1) = false := ih _ (by omega)
    have b : evo x t i = false := ih _ (by omega)
    have c : evo x t (i + 1) = false := ih _ (by omega)
    rw [a, b, c]; rfl

/-- the left edge of the single-cell pattern: nothing left of -t, and a black cell at -t -/
theorem left_edge : ∀ t : Nat, (∀ i : Int, i < -(t : Int) → evo seed0 t i = false) ∧ evo seed0 t (-(t : Int)) = true := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun i hi => ?_, by decide⟩
    show decide (i = 0) = false
    simp; omega
  | succ t ih =>
    obtain ⟨ha, hb⟩ := ih
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [evo_succ, ha (i - 1) (by omega), ha i (by omega), ha (i + 1) (by omega)]; rfl
    · rw [evo_succ]
      have e1 : -((t + 1 : Nat) : Int) - 1 = -((t : Int)) - 2 := by omega
      have e3 : -((t + 1 : Nat) : Int) + 1 = -(t : Int) := by omega
      rw [e1, e3, ha (-(t : Int) - 2) (by omega), ha (-((t + 1 : Nat) : Int)) (by omega), hb]; rfl

theorem seed_finite (t : Nat) : Fin' (evo seed0 t) :=
  ⟨t, fun i hi => support_grows seed0 0 (fun j hj => by simp [seed0]; omega) t i (by omega)⟩

theorem seed_nonzero (t : Nat) : ∃ i, evo seed0 t i = true := ⟨-(t : Int), (left_edge t).2⟩

def Problem1NonPeriodic : Prop :=
  ¬ ∃ t0 p : Nat, 0 < p ∧ ∀ t, t0 ≤ t → evo seed0 (t + p) 0 = evo seed0 t 0

def FiniteNeverPeriodic : Prop :=
  ∀ (x : Int → Bool) (p : Nat), Fin' x → (∃ i, x i = true) → 0 < p → ¬ ∀ t, evo x (t + p) 0 = evo x t 0

/-- if no nonzero finite configuration has a periodic center column, the single cell's center column is not eventually periodic -/
theorem finite_never_periodic_gives_problem1 : FiniteNeverPeriodic → Problem1NonPeriodic := by
  intro h ⟨t0, p, hp, hper⟩
  apply h (evo seed0 t0) p (seed_finite t0) (seed_nonzero t0) hp
  intro t
  have e1 : evo (evo seed0 t0) (t + p) = evo seed0 (t0 + (t + p)) := (evo_add seed0 t0 (t + p)).symm
  have e2 : evo (evo seed0 t0) t = evo seed0 (t0 + t) := (evo_add seed0 t0 t).symm
  rw [e1, e2]
  have := hper (t0 + t) (by omega)
  rw [show t0 + (t + p) = t0 + t + p by omega]; exact this

/-- NOT supported by the data in this uniform form (the gap grows slowly with r); kept because the implication to Problem 1 is formal -/
def UniformGapLemma : Prop :=
  ∀ p : Nat, 0 < p → ∃ G : Nat, ∀ (r : Nat) (x : Int → Bool), (∀ i : Int, r < i.natAbs → x i = false) → (∃ i, x i = true) →
    ¬ ∀ t, t ≤ r + G → evo x (t + p) 0 = evo x t 0

theorem gap_gives_finite_never_periodic : UniformGapLemma → FiniteNeverPeriodic := by
  intro hg x p ⟨B, hB⟩ hne hp hall
  obtain ⟨G, hG⟩ := hg p hp
  exact hG B x hB hne (fun t _ => hall t)

/-- the weaker `FiniteNeverPeriodic` already settles Problem 1 (`finite_never_periodic_gives_problem1`); this is the uniform version -/
theorem gap_gives_problem1 : UniformGapLemma → Problem1NonPeriodic := fun h => finite_never_periodic_gives_problem1 (gap_gives_finite_never_periodic h)

/-- the period-1 instance of the uniform gap lemma IS a theorem: G = 1 works (this is `no_const_column`); for periods >= 2 the uniform form is likely false -/
theorem gap_period_one : ∃ G : Nat, ∀ (r : Nat) (x : Int → Bool), (∀ i : Int, r < i.natAbs → x i = false) → (∃ i, x i = true) →
    ¬ ∀ t, t ≤ r + G → evo x (t + 1) 0 = evo x t 0 := by
  refine ⟨1, fun r x hz hne hall => ?_⟩
  have hz' : ∀ i : Int, i < -(r : Int) ∨ (r : Int) < i → x i = false := fun i hi => hz i (by omega)
  refine no_const_column x r hz' hne (evo x 0 0) (fun t ht => ?_)
  induction t with
  | zero => rfl
  | succ t ih => rw [hall t (by omega)]; exact ih (by omega)

#print axioms gap_gives_problem1
#print axioms gap_period_one
