import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardRealLine

/-! Every genuinely non-real original-field tensor in the standard Pauli
current family has a genuine non-real quaternary native-X realization.
Each descent uses the existing actual raw-card constructor and its exact
original-field correction; no coordinate cap is added as a free signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinNonrealDescent
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Pauli.ProjectiveDetermination
namespace R
export GlobalCloseCompletionKleinStandardRealLine (inclusion index dual_kernel ordered_realLine realLine_scale)
end R
namespace C
export ClosureKleinCurrent (kind cardKey rawCard_mapped dualCorrection dualCorrection_nonzero canonicalCard)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : C.kind G P torsion cardinal noncyclic=.standard)

abbrev phi : OI.K G→+*ℂ := R.inclusion.comp (ClosureSourceRows.embedding G)
abbrev complexTensor {n : ℕ} (f : Signature (OI.K G) n) := RingHomRealization.mapSignature (phi G) f

include cardinal noncyclic standard in
theorem exists_nonreal_rawCard {n : ℕ} (f : Signature (OI.K G) (n+2)) (large : 5≤n+2)
    (nonreal : ¬IsRealLine (complexTensor G f)) :
    ∃order : Equiv.Perm (Fin (n+2)),∃k : Fin 4,
      ¬IsRealLine (complexTensor G (rawCard P.family torsion f (C.cardKey G P torsion cardinal noncyclic order k))) := by
  classical
  by_contra none
  push Not at none
  apply nonreal
  apply R.ordered_realLine _ large
  intro order k
  let d := C.dualCorrection G P torsion cardinal noncyclic (R.index k)
  have hd : phi G d≠0 := (map_ne_zero _).mpr (C.dualCorrection_nonzero G P torsion cardinal noncyclic (R.index k))
  have raw := C.rawCard_mapped G P torsion cardinal noncyclic f order (R.index k)
  have rawEq (x : Fin n→Bool) :
      phi G (rawCard P.family torsion f (C.cardKey G P torsion cardinal noncyclic order (R.index k)) x)=
        phi G d*R.inclusion (C.canonicalCard G P torsion cardinal noncyclic f order (R.index k) x) := by
    have h := congrArg R.inclusion (congrFun raw x)
    simpa only [phi,d,RingHom.comp_apply,RingHomRealization.mapSignature,Pi.smul_apply,smul_eq_mul,map_mul] using h
  have scaled := R.realLine_scale (none order (R.index k)) (2/(phi G d)) (div_ne_zero (by norm_num) hd)
  convert scaled using 1
  funext x
  change Signature.contract (kernel k) (Tensor.reindex order.symm (complexTensor G f)) x=
    (2/phi G d)*phi G (rawCard P.family torsion f (C.cardKey G P torsion cardinal noncyclic order (R.index k)) x)
  rw [rawEq]
  have cancel : (2/phi G d)*(phi G d*R.inclusion (C.canonicalCard G P torsion cardinal noncyclic f order (R.index k) x))=
      2*R.inclusion (C.canonicalCard G P torsion cardinal noncyclic f order (R.index k) x) := by
    field_simp
  rw [cancel]
  simp only [C.canonicalCard,standard,RingHomRealization.mapSignature,Signature.contract,map_sum,map_mul,
    Tensor.reindex_apply,RingHom.comp_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [←mul_assoc,R.dual_kernel]

def arity : ℕ→ℕ
  | 0 => 4
  | n+1 => arity n+2

theorem arity_ge_four (n : ℕ) : 4≤arity n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => change 4≤arity n+2;omega

theorem arity_eq (n : ℕ) : arity n=2*n+4 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [arity,ih];omega

include cardinal noncyclic standard in
theorem quaternary (n : ℕ) (f : Signature (OI.K G) (arity n))
    (actual : Gadget.Realizes P.family .disequality f)
    (nonreal : ¬IsRealLine (complexTensor G f)) :
    ∃q : Signature (OI.K G) 4,Gadget.Realizes P.family .disequality q ∧ ¬IsRealLine (complexTensor G q) := by
  induction n with
  | zero => exact ⟨f,actual,nonreal⟩
  | succ n ih =>
    obtain ⟨order,k,bad⟩ := exists_nonreal_rawCard G P torsion cardinal noncyclic standard f
      (by have := arity_ge_four n;change 5≤arity n+2;omega) nonreal
    have h := rawCard_realizes_exact P.family torsion (P.retainsIdentity G)
      (by norm_num) f actual (C.cardKey G P torsion cardinal noncyclic order k)
    exact ih _ h bad

include cardinal noncyclic standard in
theorem nonreal_not_matching {n : ℕ} (f : Signature (OI.K G) n)
    (nonreal : ¬IsRealLine (complexTensor G f)) : ¬MatchingOrZero (actualTransfers P.family) f := by
  intro matching
  have h := ClosureKleinCurrent.matching_mapped G P torsion cardinal noncyclic f matching
  rw [standard] at h
  exact nonreal (GlobalCloseCompletionKleinStandardRealLine.canonical_real _ h)

structure Output where
  q : Signature (OI.K G) 4
  actual : Gadget.Realizes P.family .disequality q
  nonreal : ¬IsRealLine (complexTensor G q)
  nonmatching : ¬MatchingOrZero (actualTransfers P.family) q
  access : CurrentSignatureAccess G P (⟨4,q⟩ : AnySignature (OI.K G))

def from_retained (n : ℕ) (f : Signature (OI.K G) (arity n))
    (retained : (⟨arity n,f⟩ : AnySignature (OI.K G))∈P.family)
    (nonreal : ¬IsRealLine (complexTensor G f)) : Output G P := Classical.choice (by
  obtain ⟨q,hq,bad⟩ := quaternary G P torsion cardinal noncyclic standard n f
    (Gadget.realizes_of_mem _ .disequality f retained) nonreal
  exact ⟨⟨q,hq,bad,nonreal_not_matching G P torsion cardinal noncyclic standard q bad,
    currentSignatureAccess G P _ hq⟩⟩)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinNonrealDescent
end
