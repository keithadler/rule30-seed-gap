import Wall
import TrapData

/-!
# Rule 30: the main trap on the right

Hold the center column at 0,1,0,1,... An *event* at time `t` is: center 0 and cell 1 equal to 1
(so `e` has a one there). `trapBucket a` lists the states of cells 1..16 with age `a`, where the age counts the steps since
the last event (1,570 labelled states in all, covering 1,518 distinct states; the center value is
the parity of the age).

`TClosed`: the list is closed under one Rule 30 step for both values of cell 17, the age is updated
correctly, and an event can only follow age 5 or age 9.
`TLabeled`: ages are at most 9; at an event the age is 0 and cells 2, 3, 4 read 1, 1, 0.
Both are checked by `decide`.

`trap_forever`: once cells 1..16 are in the trap they stay in it, whatever lies further right.
`trap_cells`: at every event in the trap, cells 1..4 read 1,1,1,0.
`trap_gap`: after an event in the trap, the next event comes exactly 6 or exactly 10 steps later
(gaps 3 or 5 in `e`), with none in between.

Only the alternating center column is assumed; nothing is assumed about the left half.
This describes the right side. It does not prove that an alternating column is impossible.
-/

def isEv (c : Bool) (s : Nat) : Bool := !c && s.testBit 0

def ages : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

def TClosed : Prop :=
  ∀ a ∈ ages, ∀ s ∈ trapBucket a, ∀ f ∈ [false, true],
    if isEv (!decide (a % 2 = 1)) (wstep 16 (decide (a % 2 = 1)) s f) = true
    then (a = 5 ∨ a = 9) ∧ wstep 16 (decide (a % 2 = 1)) s f ∈ trapBucket 0
    else a + 1 ≤ 9 ∧ wstep 16 (decide (a % 2 = 1)) s f ∈ trapBucket (a + 1)

def TLabeled : Prop :=
  ∀ a ∈ ages, ∀ s ∈ trapBucket a, isEv (decide (a % 2 = 1)) s = true →
    a = 0 ∧ s.testBit 1 = true ∧ s.testBit 2 = true ∧ s.testBit 3 = false

instance : Decidable TClosed := by unfold TClosed; infer_instance
instance : Decidable TLabeled := by unfold TLabeled; infer_instance

set_option maxRecDepth 1000000 in
theorem trapT35_closed : TClosed := by decide +kernel
set_option maxRecDepth 1000000 in
theorem trapT35_labeled : TLabeled := by decide +kernel

theorem ages_mem : ∀ a : Nat, a < 10 → a ∈ ages := by decide

/-- event at time `t`: center 0 and cell 1 equal to 1 -/
def ev (x : Int → Bool) (t : Nat) : Bool := !evo x t 0 && evo x t 1

/-- cells 1..16 at time `t` are in the trap with age `a` -/
def InTrap (x : Int → Bool) (t a : Nat) : Prop :=
  a ≤ 9 ∧ evo x t 0 = decide (a % 2 = 1) ∧ ∃ s, s ∈ trapBucket a ∧ Win 16 x t s

theorem win_ev (x : Int → Bool) (t s : Nat) (h : Win 16 x t s) : isEv (evo x t 0) s = ev x t := by
  unfold isEv ev; rw [h.2 0 (by decide)]; rfl

section
variable (x : Int → Bool) (alt : ∀ t : Nat, evo x t 0 = decide (t % 2 = 1))
include alt

theorem trap_step (t a : Nat) (h : InTrap x t a) :
    InTrap x (t + 1) (if ev x (t + 1) then 0 else a + 1) ∧ (ev x (t + 1) = true → a = 5 ∨ a = 9) := by
  obtain ⟨ha, hc, s, hs, hw⟩ := h
  have f2 : evo x t ((16 : Nat) + 1 : Int) ∈ [false, true] := by
    cases evo x t ((16 : Nat) + 1 : Int) <;> simp
  have hw' := win_step 16 (by decide) x t s hw
  have h := trapT35_closed a (ages_mem a (by omega)) s hs _ f2
  have e := win_ev x (t + 1) _ hw'
  have fl := alt_flip x alt t
  rw [fl, hc] at e
  rw [hc] at hw'
  rw [e] at h
  cases he : ev x (t + 1) with
  | true =>
    rw [he] at h; simp only [ite_true] at h
    simp only [ite_true]
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨by decide, ?_, _, h2, hw'⟩, fun _ => h1⟩
    rw [fl, hc]; rcases h1 with r | r <;> subst r <;> rfl
  | false =>
    rw [he] at h; simp only [Bool.false_eq_true, ite_false] at h
    simp only [Bool.false_eq_true, ite_false]
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨h1, ?_, _, h2, hw'⟩, fun c => by cases c⟩
    rw [fl, hc]
    rcases Nat.mod_two_eq_zero_or_one a with r | r
    · rw [decide_eq_false (by omega : ¬ a % 2 = 1), decide_eq_true (by omega : (a + 1) % 2 = 1)]; rfl
    · rw [decide_eq_true r, decide_eq_false (by omega : ¬ (a + 1) % 2 = 1)]; rfl

omit alt in
theorem trap_age (t a : Nat) (h : InTrap x t a) : a ≤ 9 := by
  exact h.1

/-- once in the trap, always in the trap -/
theorem trap_forever (t a : Nat) (h : InTrap x t a) : ∀ n : Nat, ∃ a', InTrap x (t + n) a' := by
  intro n
  induction n with
  | zero => exact ⟨a, h⟩
  | succ n ih =>
    obtain ⟨a', h'⟩ := ih
    exact ⟨_, (trap_step x alt (t + n) a' h').1⟩

omit alt in
/-- at an event in the trap the age is 0 and cells 1..4 read 1,1,1,0 -/
theorem trap_cells (t a : Nat) (h : InTrap x t a) (he : ev x t = true) :
    a = 0 ∧ evo x t 1 = true ∧ evo x t 2 = true ∧ evo x t 3 = true ∧ evo x t 4 = false := by
  obtain ⟨ha, hc, s, hs, hw⟩ := h
  have hl := trapT35_labeled a (ages_mem a (by omega)) s hs (by rw [← hc, win_ev x t s hw]; exact he)
  obtain ⟨h0, h1, h2, h3⟩ := hl
  have c1 : evo x t 1 = true := by
    unfold ev at he; cases h : evo x t 1 <;> simp [h] at he ⊢
  have b1 := hw.2 1 (by decide)
  have b2 := hw.2 2 (by decide)
  have b3 := hw.2 3 (by decide)
  rw [h1] at b1; rw [h2] at b2; rw [h3] at b3
  exact ⟨h0, c1, b1.symm, b2.symm, b3.symm⟩

theorem trap_no (t a : Nat) (h : InTrap x t a) (h5 : a ≠ 5) (h9 : a ≠ 9) :
    ev x (t + 1) = false ∧ InTrap x (t + 1) (a + 1) := by
  obtain ⟨h1, h2⟩ := trap_step x alt t a h
  cases he : ev x (t + 1) with
  | true => rcases h2 he with r | r <;> contradiction
  | false => rw [he] at h1; exact ⟨rfl, h1⟩

/-- after an event in the trap, the next event is exactly 6 or exactly 10 steps later -/
theorem trap_gap (t a : Nat) (h : InTrap x t a) (he : ev x t = true) :
    ev x (t + 1) = false ∧ ev x (t + 2) = false ∧ ev x (t + 3) = false ∧ ev x (t + 4) = false ∧
    ev x (t + 5) = false ∧
    (ev x (t + 6) = true ∨
      (ev x (t + 6) = false ∧ ev x (t + 7) = false ∧ ev x (t + 8) = false ∧ ev x (t + 9) = false ∧
        ev x (t + 10) = true)) := by
  have a0 := (trap_cells x t a h he).1
  subst a0
  obtain ⟨e1, s1⟩ := trap_no x alt t 0 h (by decide) (by decide)
  obtain ⟨e2, s2⟩ := trap_no x alt (t + 1) 1 s1 (by decide) (by decide)
  obtain ⟨e3, s3⟩ := trap_no x alt (t + 2) 2 s2 (by decide) (by decide)
  obtain ⟨e4, s4⟩ := trap_no x alt (t + 3) 3 s3 (by decide) (by decide)
  obtain ⟨e5, s5⟩ := trap_no x alt (t + 4) 4 s4 (by decide) (by decide)
  refine ⟨e1, e2, e3, e4, e5, ?_⟩
  cases e6 : ev x (t + 6) with
  | true => exact Or.inl rfl
  | false =>
    have s6 := (trap_step x alt (t + 5) 5 s5).1
    rw [(by omega : t + 5 + 1 = t + 6), e6] at s6
    obtain ⟨e7, s7⟩ := trap_no x alt (t + 6) 6 s6 (by decide) (by decide)
    obtain ⟨e8, s8⟩ := trap_no x alt (t + 7) 7 s7 (by decide) (by decide)
    obtain ⟨e9, s9⟩ := trap_no x alt (t + 8) 8 s8 (by decide) (by decide)
    refine Or.inr ⟨rfl, e7, e8, e9, ?_⟩
    cases e10 : ev x (t + 10) with
    | true => rfl
    | false =>
      have s10 := (trap_step x alt (t + 9) 9 s9).1
      rw [(by omega : t + 9 + 1 = t + 10), e10] at s10
      have := trap_age x (t + 10) _ s10
      simp at this
end

#print axioms trap_forever
#print axioms trap_cells
#print axioms trap_gap
