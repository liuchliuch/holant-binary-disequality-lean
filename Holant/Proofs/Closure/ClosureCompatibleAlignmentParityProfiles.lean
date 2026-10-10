import Holant.Proofs.Closure.ClosureCompatibleAlignmentParity
import Holant.Proofs.Closure.ClosureCompatibleAlignmentTags
import Holant.Proofs.Closure.ClosureCompatibleAlignmentCurrent

/-! Support-parity profiles of the literal selected coefficient products.
Their total parity is derived from the actual original ancestor, including
zero endpoints; no protected-factor parity is assumed as an extra oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open ClosureSixPort (Word bit parity)

theorem hasParity_supported_xor {α : Bool} {A : Mat} (support : HasParity α A)
    (a b : Bool) (nonzero : A a b ≠ 0) : (a ^^ b) = α := by
  obtain ⟨w,_,rfl⟩ := support
  cases α <;> cases a <;> cases b <;> simp_all [monomial]

theorem product_support_parity {n r : ℕ} (p : (Fin r × Bool) ≃ Fin n)
    (A : Fin r → Mat) (κ : Scalar) (α : Fin r → Bool)
    (support : ∀ e,HasParity (α e) (A e)) (x : Word n)
    (nonzero : productValue p A κ x ≠ 0) : parity x = ∑ e,bit (α e) := by
  have factors : (∏ e,A e (x (p (e,false))) (x (p (e,true)))) ≠ 0 := (mul_ne_zero_iff.mp nonzero).2
  have endpoints (e : Fin r) : (x (p (e,false)) ^^ x (p (e,true))) = α e :=
    hasParity_supported_xor (support e) _ _ ((Finset.prod_ne_zero_iff.mp factors) e (Finset.mem_univ e))
  unfold parity
  rw [← Equiv.sum_comp p (fun i => bit (x i)),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Fintype.sum_bool]
  rw [ClosureSixPort.bit_xor,Bool.xor_comm,endpoints e]

theorem projective_parities_equal {α β : Bool} {A B : Mat}
    (first : HasParity α A) (second : HasParity β B) (line : ProjectivelyEqual B A) : β = α := by
  by_contra different
  have opposite : β = !α := by cases value : α <;> cases β <;> simp_all
  apply opposite_parities_not_projective first (by simpa only [opposite] using second)
  exact line

theorem bit_injective : Function.Injective bit := by
  intro a b same
  cases a <;> cases b <;> simpa [bit] using same

/-- If every outside line agrees, equal total support parity forces the
remaining protected parity to agree as well. -/
theorem profiles_equal_of_one_possible_change {r : ℕ} (α β : Fin r → Bool) (e : Fin r)
    (outside : ∀ j,j ≠ e → β j = α j)
    (total : (∑ j,bit (α j)) = ∑ j,bit (β j)) : β e = α e := by
  have rest : (∑ j ∈ {e}ᶜ,bit (α j)) = ∑ j ∈ {e}ᶜ,bit (β j) := by
    apply Finset.sum_congr rfl
    intro j member
    rw [outside j (by simpa using member)]
  rw [Fintype.sum_eq_add_sum_compl e,Fintype.sum_eq_add_sum_compl e,rest] at total
  exact bit_injective (add_right_cancel total).symm

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))

theorem normalizedCurrentCard_entry (γ : Bool) (t : {t : Scalar // Roots N.m t}) (x : Word (2*r+2)) :
    normalizedCurrentCard G P torsion N f order γ t x =
      ClosureSourceRows.embedding G (f (fillPairN order false γ x)) +
        t.val*ClosureSourceRows.embedding G (f (fillPairN order true γ x)) := by
  change normalizedCurrentCard G P torsion N f order γ t x =
    ClosureSourceRows.embedding G (f (fun i =>
      (Fin.cons false (Fin.cons (false ^^ γ) x) : ClosureSixPort.Word (2*r+4)) (order.symm i))) +
      t.val*ClosureSourceRows.embedding G (f (fun i =>
        (Fin.cons true (Fin.cons (true ^^ γ) x) : ClosureSixPort.Word (2*r+4)) (order.symm i)))
  cases γ <;> simp [normalizedCurrentCard,Signature.contract,Tensor.reindex,
    RingHomRealization.mapSignature,M,monomial,Fintype.sum_bool] <;> ring

theorem normalizedCurrentCard_supported_parity (γ : Bool) (t : {t : Scalar // Roots N.m t})
    (global : ZMod 2) (support : ∀ w : Word (2*r+4),parity w ≠ global → f w = 0)
    (x : Word (2*r+2)) (nonzero : normalizedCurrentCard G P torsion N f order γ t x ≠ 0) :
    bit γ+parity x = global := by
  have endpoint : ∃ a : Bool,f (fillPairN order a γ x) ≠ 0 := by
    by_contra none
    push_neg at none
    apply nonzero
    rw [normalizedCurrentCard_entry,none false,none true]
    simp
  obtain ⟨a,live⟩ := endpoint
  have same : parity (fillPairN order a γ x) = global := by
    by_contra different
    exact live (support _ different)
  simpa only [parity_fillPairN] using same

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
