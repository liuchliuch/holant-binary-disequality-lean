import Holant.Realization
import Holant.TensorClosure
import Mathlib.Data.Multiset.Sum
import Mathlib.Order.WellFounded


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

noncomputable section
variable {L : Type*} [Field L]

/-- A genuine split retains the disjoint port partition and nonzero scalar. -/
structure ProperSplit (f a b : AnySignature L) where
  left_pos : 0 < a.1
  right_pos : 0 < b.1
  ports : (Fin a.1 ⊕ Fin b.1) ≃ Fin f.1
  scale : Lˣ
  equation : f.2 = fun x => (scale : L) *
    (a.2 (fun i => x (ports (.inl i))) * b.2 (fun i => x (ports (.inr i))))

theorem ProperSplit.arity {f a b : AnySignature L} (s : ProperSplit f a b) :
    a.1 + b.1 = f.1 := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr s.ports

theorem ProperSplit.left_lt {f a b : AnySignature L} (s : ProperSplit f a b) :
    a.1 < f.1 := by have := s.arity; have := s.right_pos; omega

theorem ProperSplit.right_lt {f a b : AnySignature L} (s : ProperSplit f a b) :
    b.1 < f.1 := by have := s.arity; have := s.left_pos; omega

theorem ProperSplit.factors_nonzero {f a b : AnySignature L} (s : ProperSplit f a b)
    (hf : f.2 ≠ 0) : a.2 ≠ 0 ∧ b.2 ≠ 0 := by
  constructor
  · intro ha
    apply hf
    rw [s.equation, ha]
    funext x
    simp
  · intro hb
    apply hf
    rw [s.equation, hb]
    funext x
    simp

/-- Positive-arity tensor primality, with every ordered nontrivial two-block
factorization excluded.  This is a local mathematical predicate, not an access
or complexity assertion. -/
def Prime (f : AnySignature L) : Prop :=
  f.2 ≠ 0 ∧ ¬ ∃ a b, Nonempty (ProperSplit f a b)

inductive FactorTree : AnySignature L → Type _
  | leaf (f : AnySignature L) (prime : Prime f) : FactorTree f
  | split {f a b : AnySignature L} (data : ProperSplit f a b)
      (left : FactorTree a) (right : FactorTree b) : FactorTree f

/-- Existence of a finite exact factor tree follows from arity induction,
without assuming a factorization-completeness theorem.  This construction is
classical; it is not claimed to be an implemented polynomial-time procedure. -/
theorem exists_factorTree (f : AnySignature L) (hf : f.2 ≠ 0) : Nonempty (FactorTree f) := by
  classical
  suffices h : ∀ n, ∀ f : AnySignature L, f.1 = n → f.2 ≠ 0 → Nonempty (FactorTree f) from
    h f.1 f rfl hf
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro f hfn hf
      by_cases hs : ∃ a b, Nonempty (ProperSplit f a b)
      · obtain ⟨a, b, ⟨s⟩⟩ := hs
        obtain ⟨ta⟩ := ih a.1 (hfn ▸ s.left_lt) a rfl (s.factors_nonzero hf).1
        obtain ⟨tb⟩ := ih b.1 (hfn ▸ s.right_lt) b rfl (s.factors_nonzero hf).2
        exact ⟨.split s ta tb⟩
      · exact ⟨.leaf f ⟨hf, hs⟩⟩

def FactorTree.leaves {f : AnySignature L} : FactorTree f → Multiset (AnySignature L)
  | .leaf f _ => {f}
  | .split _ a b => a.leaves + b.leaves

theorem FactorTree.leaves_prime {f : AnySignature L} (t : FactorTree f)
    (a : AnySignature L) (ha : a ∈ t.leaves) : Prime a := by
  induction t with
  | leaf f hp =>
      have he : a = f := by simpa only [FactorTree.leaves, Multiset.mem_singleton] using ha
      subst a
      exact hp
  | split s ta tb iha ihb =>
      rcases Multiset.mem_add.mp ha with ha | hb
      · exact iha ha
      · exact ihb hb

def factorPotential (W : Multiset (AnySignature L)) : ℕ :=
  (W.map (fun f => f.1 - 1)).sum

@[simp] theorem factorPotential_zero : factorPotential (0 : Multiset (AnySignature L)) = 0 := rfl

@[simp] theorem factorPotential_add (W V : Multiset (AnySignature L)) :
    factorPotential (W + V) = factorPotential W + factorPotential V := by
  simp [factorPotential]

@[simp] theorem factorPotential_cons (f : AnySignature L) (W : Multiset (AnySignature L)) :
    factorPotential (f ::ₘ W) = (f.1 - 1) + factorPotential W := by
  simp [factorPotential]

/-- Nullary scalars and certified unary factors do not enter the open queue. -/
def pending (f : AnySignature L) : Multiset (AnySignature L) :=
  if 2 ≤ f.1 then {f} else 0

@[simp] theorem factorPotential_pending (f : AnySignature L) :
    factorPotential (pending f) = f.1 - 1 := by
  by_cases h : 2 ≤ f.1
  · simp [pending, h, factorPotential]
  · have hz : f.1 - 1 = 0 := by omega
    simp [pending, h, hz]

/-- Each genuine split lowers the potential by exactly one, even when one
or both children are unary and never enter the unresolved worklist. -/
theorem split_potential_drop {f a b : AnySignature L} (s : ProperSplit f a b)
    (W : Multiset (AnySignature L)) :
    factorPotential (pending a + pending b + W) + 1 = factorPotential (f ::ₘ W) := by
  simp only [factorPotential_add, factorPotential_pending, factorPotential_cons]
  have := s.arity
  have := s.left_pos
  have := s.right_pos
  omega

/-- Actual queue operations.  Strict potential decrease is a theorem below,
not a constructor argument.  Certification also requires mathematical primality. -/
inductive FactorStep : Multiset (AnySignature L) → Multiset (AnySignature L) → Prop
  | certify (f : AnySignature L) (W) (hn : 2 ≤ f.1) (hp : Prime f) :
      FactorStep W (f ::ₘ W)
  | split {f a b : AnySignature L} (s : ProperSplit f a b) (W) :
      FactorStep (pending a + pending b + W) (f ::ₘ W)

theorem factorStep_decreases {W V : Multiset (AnySignature L)} (h : FactorStep W V) :
    factorPotential W < factorPotential V := by
  cases h with
  | certify f W hn hp => simp only [factorPotential_cons]; omega
  | split s W => have := split_potential_drop s W; omega

theorem factorStep_wellFounded : WellFounded (FactorStep (L := L)) :=
  Subrelation.wf (fun h => factorStep_decreases h) (measure factorPotential).wf

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
