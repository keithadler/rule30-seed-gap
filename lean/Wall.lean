import Repeat
import WallData

/-!
# Rule 30: walls on the right exclude a seed for every left width

Hold the center column at 0,1,0,1,... and watch cells 1..k to its right. `wstep` is one Rule 30 step
of those k cells written on a natural number (cell 1 = lowest bit), given the center value `c` and
the value `f` of cell k+1.

A *wall* is a finite list `T` of (phase, center value, cells 1..k) that is closed under `wstep` for
both values of cell k+1, with the phase advancing by one modulo `m` and cell 1 a function of the phase.
Once the cells are in a wall, column 1 is periodic forever, whatever lies further right.

`wall_excluded`: a row with a leftmost one and an alternating center column can never have its
cells 1..k in a wall. (Column 1 periodic makes column -1 periodic at even times, which
`alt_e_never_periodic` forbids.)

`wallT2_excluded`, `wallT2b_excluded`, `wallT2c_excluded`, `wallT25_excluded`: four concrete walls,
with `Closed` and `Labeled` checked by `decide`.

This excludes infinitely many seeds for all time. It does not prove that an alternating column is impossible.
-/

def wstep (k : Nat) (c : Bool) (s : Nat) (f : Bool) : Nat :=
  (((s <<< 1) ||| c.toNat) ^^^ ((s ||| (f.toNat <<< k)) ||| ((s ||| (f.toNat <<< k)) >>> 1))) &&& (2 ^ k - 1)

/-- `s` holds cells 1..k of the row at time `t` -/
def Win (k : Nat) (x : Int → Bool) (t s : Nat) : Prop :=
  s < 2 ^ k ∧ ∀ i : Nat, i < k → s.testBit i = evo x t ((i : Int) + 1)

def Closed (k m : Nat) (T : List (Nat × Bool × Nat)) : Prop :=
  ∀ p ∈ T, ∀ f ∈ [false, true], ((p.1 + 1) % m, !p.2.1, wstep k p.2.1 p.2.2 f) ∈ T

def Labeled (m w : Nat) (T : List (Nat × Bool × Nat)) : Prop :=
  ∀ p ∈ T, p.1 < m ∧ p.2.2.testBit 0 = w.testBit p.1

instance (k m T) : Decidable (Closed k m T) := by unfold Closed; infer_instance
instance (m w T) : Decidable (Labeled m w T) := by unfold Labeled; infer_instance

theorem toNat_testBit_zero (c : Bool) : c.toNat.testBit 0 = c := by cases c <;> rfl
theorem toNat_testBit_succ (c : Bool) (i : Nat) : c.toNat.testBit (i + 1) = false := by
  cases c <;> simp [Nat.testBit_succ]

theorem full_lo (k s i : Nat) (f : Bool) (h : i < k) : (s ||| (f.toNat <<< k)).testBit i = s.testBit i := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, decide_eq_false (by omega : ¬ i ≥ k)]; simp
theorem full_hi (k s : Nat) (f : Bool) (h : s < 2 ^ k) : (s ||| (f.toNat <<< k)).testBit k = f := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_lt_two_pow h]; cases f <;> simp

theorem wstep_lt (k : Nat) (c : Bool) (s : Nat) (f : Bool) : wstep k c s f < 2 ^ k := by
  unfold wstep
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos k) (by decide))

theorem wstep_bit (k : Nat) (c : Bool) (s : Nat) (f : Bool) (i : Nat) (h : i < k) :
    (wstep k c s f).testBit i =
      xor (((s <<< 1) ||| c.toNat).testBit i)
        ((s ||| (f.toNat <<< k)).testBit i || (s ||| (f.toNat <<< k)).testBit (i + 1)) := by
  unfold wstep
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true h, Bool.and_true,
    Nat.testBit_xor, Nat.testBit_or (s ||| _) , Nat.testBit_shiftRight, Nat.add_comm 1 i]

theorem win_step (k : Nat) (hk : 0 < k) (x : Int → Bool) (t s : Nat) (h : Win k x t s) :
    Win k x (t + 1) (wstep k (evo x t 0) s (evo x t ((k : Int) + 1))) := by
  obtain ⟨hs, hb⟩ := h
  refine ⟨wstep_lt _ _ _ _, fun i hi => ?_⟩
  rw [wstep_bit k _ s _ i hi, full_lo k s i _ hi]
  have hr : (s ||| ((evo x t ((k : Int) + 1)).toNat <<< k)).testBit (i + 1) = evo x t ((i : Int) + 1 + 1) := by
    by_cases hik : i + 1 < k
    · rw [full_lo k s (i + 1) _ hik, hb (i + 1) hik]; congr 1
    · have e : i + 1 = k := by omega
      subst e; rw [full_hi _ s _ hs]; congr 1
  rw [hr, hb i hi, evo_at x t ((i : Int) + 1) (i : Int) ((i : Int) + 1 + 1) (by omega) rfl]
  congr 1
  cases i with
  | zero => rw [Nat.testBit_or, toNat_testBit_zero]; simp
  | succ j =>
    rw [Nat.testBit_or, toNat_testBit_succ, Bool.or_false, Nat.testBit_shiftLeft]
    simp
    rw [hb j (by omega)]

theorem alt_flip (x : Int → Bool) (alt : ∀ t : Nat, evo x t 0 = decide (t % 2 = 1)) (t : Nat) :
    evo x (t + 1) 0 = !evo x t 0 := by
  rw [alt, alt]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [decide_eq_true (by omega : (t + 1) % 2 = 1), decide_eq_false (by omega : ¬ t % 2 = 1)]; rfl
  · rw [decide_eq_false (by omega : ¬ (t + 1) % 2 = 1), decide_eq_true h]; rfl

/-- a row with a leftmost one and an alternating center column never has cells 1..k in a wall -/
theorem wall_excluded (k m w : Nat) (T : List (Nat × Bool × Nat)) (hk : 0 < k) (hm : 0 < m)
    (hc : Closed k m T) (hl : Labeled m w T)
    (x : Int → Bool) (W : Int) (hz : ∀ j, j < -W → x j = false) (hW : x (-W) = true)
    (alt : ∀ t : Nat, evo x t 0 = decide (t % 2 = 1))
    (t0 ph s : Nat) (hin : (ph, evo x t0 0, s) ∈ T) (hw : Win k x t0 s) : False := by
  have inv : ∀ n : Nat, ∃ p s', (p, evo x (t0 + n) 0, s') ∈ T ∧ p % m = (ph + n) % m ∧ Win k x (t0 + n) s' := by
    intro n
    induction n with
    | zero => exact ⟨ph, s, hin, rfl, hw⟩
    | succ n ih =>
      obtain ⟨p, s', hp, hph, hwin⟩ := ih
      have f2 : evo x (t0 + n) ((k : Int) + 1) ∈ [false, true] := by
        cases evo x (t0 + n) ((k : Int) + 1) <;> simp
      have h := hc _ hp _ f2
      refine ⟨(p + 1) % m, _, ?_, ?_, win_step k hk x (t0 + n) s' hwin⟩
      · rw [(by omega : t0 + (n + 1) = t0 + n + 1), alt_flip x alt]; exact h
      · rw [Nat.mod_mod, Nat.add_mod, hph, ← Nat.add_mod]; rfl
  have col : ∀ n : Nat, evo x (t0 + n) 1 = w.testBit ((ph + n) % m) := by
    intro n
    obtain ⟨p, s', hp, hph, hwin⟩ := inv n
    obtain ⟨hlt, hbit⟩ := hl _ hp
    have h1 := hwin.2 0 hk
    rw [← hph, Nat.mod_eq_of_lt hlt, ← hbit, h1]; rfl
  have per : ∀ t : Nat, t0 ≤ t → evo x (t + 2 * m) 1 = evo x t 1 := by
    intro t ht
    have a := col (t - t0)
    have b := col (t - t0 + 2 * m)
    rw [(by omega : t0 + (t - t0) = t)] at a
    rw [(by omega : t0 + (t - t0 + 2 * m) = t + 2 * m), (by omega : ph + (t - t0 + 2 * m) = ph + (t - t0) + 2 * m),
      Nat.add_mul_mod_self_right] at b
    rw [a, b]
  have neg : ∀ s : Nat, evo x (2 * s) (-1) = !evo x (2 * s) 1 := by
    intro s
    have h := evo_at x (2 * s) 0 (-1) 1 (by omega) (by omega)
    rw [alt (2 * s + 1), alt (2 * s), decide_eq_true (by omega : (2 * s + 1) % 2 = 1),
      decide_eq_false (by omega : ¬ (2 * s) % 2 = 1)] at h
    exact p2_a _ _ h
  refine alt_e_never_periodic x W hz hW alt t0 m hm (fun s hs => ?_)
  rw [neg, neg, (by omega : 2 * (s + m) = 2 * s + 2 * m), per (2 * s) (by omega)]

set_option maxRecDepth 100000 in
theorem wallT2_closed : Closed wallT2_k wallT2_m wallT2 := by decide
set_option maxRecDepth 100000 in
theorem wallT2_labeled : Labeled wallT2_m wallT2_w wallT2 := by decide
set_option maxRecDepth 100000 in
theorem wallT2b_closed : Closed wallT2b_k wallT2b_m wallT2b := by decide
set_option maxRecDepth 100000 in
theorem wallT2b_labeled : Labeled wallT2b_m wallT2b_w wallT2b := by decide
set_option maxRecDepth 100000 in
theorem wallT2c_closed : Closed wallT2c_k wallT2c_m wallT2c := by decide
set_option maxRecDepth 100000 in
theorem wallT2c_labeled : Labeled wallT2c_m wallT2c_w wallT2c := by decide
set_option maxRecDepth 100000 in
theorem wallT25_closed : Closed wallT25_k wallT25_m wallT25 := by decide
set_option maxRecDepth 100000 in
theorem wallT25_labeled : Labeled wallT25_m wallT25_w wallT25 := by decide

section
variable (x : Int → Bool) (W : Int) (hz : ∀ j, j < -W → x j = false) (hW : x (-W) = true)
  (alt : ∀ t : Nat, evo x t 0 = decide (t % 2 = 1))
include hz hW alt

theorem wallT2_excluded (t0 ph s : Nat) (hin : (ph, evo x t0 0, s) ∈ wallT2) (hw : Win 19 x t0 s) : False :=
  wall_excluded 19 8 wallT2_w wallT2 (by decide) (by decide) wallT2_closed wallT2_labeled x W hz hW alt t0 ph s hin hw
theorem wallT2b_excluded (t0 ph s : Nat) (hin : (ph, evo x t0 0, s) ∈ wallT2b) (hw : Win 26 x t0 s) : False :=
  wall_excluded 26 8 wallT2b_w wallT2b (by decide) (by decide) wallT2b_closed wallT2b_labeled x W hz hW alt t0 ph s hin hw
theorem wallT2c_excluded (t0 ph s : Nat) (hin : (ph, evo x t0 0, s) ∈ wallT2c) (hw : Win 33 x t0 s) : False :=
  wall_excluded 33 8 wallT2c_w wallT2c (by decide) (by decide) wallT2c_closed wallT2c_labeled x W hz hW alt t0 ph s hin hw
theorem wallT25_excluded (t0 ph s : Nat) (hin : (ph, evo x t0 0, s) ∈ wallT25) (hw : Win 31 x t0 s) : False :=
  wall_excluded 31 14 wallT25_w wallT25 (by decide) (by decide) wallT25_closed wallT25_labeled x W hz hW alt t0 ph s hin hw
end

/-- A concrete instance. If cells 1..19 of a row with a leftmost one read
`1001100101011000000` (the bits of 6809, cell 1 first), whatever the other cells are,
the center column is not 0,1,0,1,... forever. -/
theorem wallT2_example (x : Int → Bool) (W : Int) (hz : ∀ j, j < -W → x j = false) (hW : x (-W) = true)
    (h : ∀ i : Nat, i < 19 → x ((i : Int) + 1) = Nat.testBit 6809 i) :
    ¬ ∀ t : Nat, evo x t 0 = decide (t % 2 = 1) := by
  intro alt
  refine wallT2_excluded x W hz hW alt 0 0 6809 ?_ ⟨by decide, fun i hi => (h i hi).symm⟩
  rw [alt 0]; decide

#print axioms wall_excluded
#print axioms wallT2_excluded
#print axioms wallT25_excluded
#print axioms wallT2_example
