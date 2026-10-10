import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineParityMatching
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinQuaternaryRestart

/-! Every actual even row with mixed support parity yields an actual
nonmatching quaternary in the unchanged original family. All Pauli contractions
and scalar corrections come from the complete standard current group. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineParityActual
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Pauli.ProjectiveDetermination
open GlobalCloseCompletionKleinHigherNonaffineParity
open GlobalCloseCompletionKleinHigherNonaffineParityMatching
namespace R
export GlobalCloseCompletionKleinStandardRealLine (inclusion index dual_kernel)
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
theorem exists_nonparity_rawCard {n : ℕ} (f : Signature (OI.K G) (n+2)) (large : 5≤n+2)
    (nonparity : ¬HasParity (complexTensor G f)) :
    ∃order : Equiv.Perm (Fin (n+2)),∃k : Fin 4,
      ¬HasParity (complexTensor G (rawCard P.family torsion f (C.cardKey G P torsion cardinal noncyclic order k))) := by
  classical
  by_contra none
  push Not at none
  apply nonparity
  apply ordered_parity _ large
  intro order k
  let d := C.dualCorrection G P torsion cardinal noncyclic (R.index k)
  have hd : phi G d≠0 := (map_ne_zero _).mpr (C.dualCorrection_nonzero G P torsion cardinal noncyclic (R.index k))
  have raw := C.rawCard_mapped G P torsion cardinal noncyclic f order (R.index k)
  have rawEq (x : Fin n→Bool) :
      phi G (rawCard P.family torsion f (C.cardKey G P torsion cardinal noncyclic order (R.index k)) x)=
        phi G d*R.inclusion (C.canonicalCard G P torsion cardinal noncyclic f order (R.index k) x) := by
    have h := congrArg R.inclusion (congrFun raw x)
    simpa only [phi,d,RingHom.comp_apply,RingHomRealization.mapSignature,Pi.smul_apply,smul_eq_mul,map_mul] using h
  have scaled := scale_parity _ (none order (R.index k)) (2/(phi G d))
  convert scaled using 1
  funext x
  change Signature.contract (kernel k) (Tensor.reindex order.symm (complexTensor G f)) x=
    (2/phi G d)*phi G (rawCard P.family torsion f (C.cardKey G P torsion cardinal noncyclic order (R.index k)) x)
  rw [rawEq]
  have cancel : (2/phi G d)*(phi G d*R.inclusion (C.canonicalCard G P torsion cardinal noncyclic f order (R.index k) x))=
      2*R.inclusion (C.canonicalCard G P torsion cardinal noncyclic f order (R.index k) x) := by
    field_simp [hd]
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
    (nonparity : ¬HasParity (complexTensor G f)) :
    ∃q : Signature (OI.K G) 4,Gadget.Realizes P.family .disequality q ∧ ¬HasParity (complexTensor G q) := by
  induction n with
  | zero => exact ⟨f,actual,nonparity⟩
  | succ n ih =>
    obtain ⟨order,k,bad⟩ := exists_nonparity_rawCard G P torsion cardinal noncyclic standard f
      (by have := arity_ge_four n;change 5≤arity n+2;omega) nonparity
    have h := rawCard_realizes_exact P.family torsion (P.retainsIdentity G)
      (by norm_num) f actual (C.cardKey G P torsion cardinal noncyclic order k)
    exact ih _ h bad

include cardinal noncyclic standard in
theorem nonparity_not_matching {n : ℕ} (f : Signature (OI.K G) n)
    (nonparity : ¬HasParity (complexTensor G f)) : ¬MatchingOrZero (actualTransfers P.family) f := by
  intro matching
  have h := ClosureKleinCurrent.matching_mapped G P torsion cardinal noncyclic f matching
  rw [standard] at h
  exact nonparity (GlobalCloseCompletionKleinHigherNonaffineParityMatching.pauli_parity _
    (GlobalCloseCompletionKleinHigherNonaffineCurrent.canonical_pauli _ h))

def from_actual (n : ℕ) (f : Signature (OI.K G) (arity n))
    (actual : Gadget.Realizes P.family .disequality f)
    (nonparity : ¬HasParity (complexTensor G f)) : GlobalCloseCompletionKleinQuaternaryRestart.D.Output G P :=
  Classical.choice (by
    obtain ⟨q,hq,bad⟩ := quaternary G P torsion cardinal noncyclic standard n f actual nonparity
    exact ⟨⟨q,hq,nonparity_not_matching G P torsion cardinal noncyclic standard q bad⟩⟩)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineParityActual
end
