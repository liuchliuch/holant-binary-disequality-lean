import Holant.Complexity.UniversalPairReduction.OrderedGadget
import Holant.Complexity.UniversalPairReduction.RawHole

/-! Exact denotation of the literal ordered query records. This is independent
of any tractability assumption and retains the original graph sum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction
open FixedGadgetSubstitution
open scoped BigOperators

variable {K : Type} [CommSemiring K]

/-- Changing just the marked factor contracts its raw hole against the new
ordered binary table. The same hole therefore applies to both B orientations. -/
theorem denote_binary_relabel (s : NetworkShape 0)
    (f g : (u : Fin s.vertices) → Signature K (s.arity u))
    (E : Fin s.edges → Bool → Bool → K) (v : Fin s.vertices)
    (h : s.arity v=2) (hv : ∀u, u≠v → f u=g u) :
    (Network.mk s g E).denote Fin.elim0 =
      (binaryRaw (Network.mk s f E) v h).insert
        (fun a b => g v (fun i => (![a,b] : Fin 2 → Bool) (Fin.cast h i))) := by
  rw [denote_eq_binary_insert (Network.mk s g E) v h]
  have hh := rawHole_congr s f g E v hv
  unfold binaryRaw
  rw [←hh]

namespace OrderedQueries
variable {s b : ℕ} {arity : ℕ → ℕ} {S : NetworkShape 2}
variable (L : Labelling S s b arity) (p : Equiv.Perm (Fin 2))

 theorem arity_eq : sourceArity (templates L p) = extendedArity s arity := by
  funext i
  by_cases h : i<s
  · simp [sourceArity,templates,Adjoin.templates,h,identityTemplate,extendedArity]
  · simp [sourceArity,templates,Adjoin.templates,h,extendedArity,Labelling.template]

variable (signatures : (i : Fin s) → Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)

def sourceSignatures (i : Fin (s+1)) : Signature K (sourceArity (templates L p) i.val) :=
  ((templates L p i.val).network (valid L p i.val i.isLt).1 signatures kernels).denote

/-- This source value is interpreted from precisely the original raw record,
with only the distinguished signature replaced by the fixed physical gadget. -/
def sourceValue (r : Input (s:=s) (b:=b) (arity:=arity)) : K :=
  (r.val.realize (by rw [arity_eq]; exact r.property)
    (sourceSignatures L p signatures kernels) kernels).denote Fin.elim0

 theorem query_value (r : Input (s:=s) (b:=b) (arity:=arity)) :
    ((query L p r).val.realize (query L p r).property signatures kernels).denote Fin.elim0 =
      sourceValue L p signatures kernels r := by
  let hr : r.val.WellFormed (s+1) b (sourceArity (templates L p)) := by
    rw [arity_eq]
    exact r.property
  have he := replacement_partition (templates L p) r.val hr
    (fun i hi => (valid L p i hi).1)
    (sourceSignatures L p signatures kernels) signatures kernels (fun _ => (1:K))
    (fun i => by simp [sourceSignatures])
  simpa only [Pi.one_apply,Finset.prod_const_one,one_mul,sourceValue,query,Compiler.value] using he

/-- The actual minus-orientation macro swaps the two external bit arguments. -/
theorem reverse_macro (a c : Bool) :
    (((permuteLabelling L (Equiv.swap 0 1)).template).network
      (permuteLabelling L (Equiv.swap 0 1)).wellFormed signatures kernels).denote ![a,c] =
      (L.sourceNetwork signatures kernels).denote ![c,a] := by
  rw [template_permute]
  congr 1
  funext i
  fin_cases i <;> simp

end OrderedQueries
end Holant.Complexity.UniversalPairReduction
