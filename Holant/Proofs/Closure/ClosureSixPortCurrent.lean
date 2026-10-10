import Holant.Proofs.Closure.ClosureSixPortParity
import Holant.Proofs.Closure.ClosureSourceRowsMonomial
import Holant.Proofs.Closure.DeckContraction
import Holant.Proofs.Closure.ClosurePhysicalBridge
import Holant.Marked.SupportAtlas.MarkedDeck

/-! NEW UNVERIFIED exact CURRENT native-M bridge. Complex roots are lifted
algebraically and select actual ORIGINAL-field complete-group keys. All scalar
multipliers, the native-X sandwich, and the inverse even phase are recorded. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Tractable Holant.Algebraic Holant.Projective Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Marked Holant.Marked.SupportAtlas
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapSignature)
end RH

/-- Nonzero scalar normalization changes only the recorded global coefficient. -/
theorem rootMatching_smul {n m : ℕ} {q : Signature ℂ n}
    (hq : RootMatching m q) (c : ℂ) (hc : c ≠ 0) : RootMatching m (c • q) := by
  rcases hq with ⟨M,mono,scalar,he⟩
  let N : Presentation ℂ (Fin n) := { M with scalar := c * M.scalar }
  refine ⟨N,mono,mul_ne_zero hc scalar,?_⟩
  rw [he]
  funext x
  change c * (M.scalar * _) = (c * M.scalar) * _
  ring

theorem rootMatchingOrZero_unscale {n m : ℕ} {q : Signature ℂ n}
    (c : ℂ) (hc : c ≠ 0) (hq : c • q = 0 ∨ RootMatching m (c • q)) :
    q = 0 ∨ RootMatching m q := by
  rcases hq with hz | hq
  · left
    exact (smul_eq_zero.mp hz).resolve_left hc
  · right
    have hi := rootMatching_smul hq c⁻¹ (inv_ne_zero hc)
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hi

theorem matrix_Xsandwich {L : Type*} [Field L]
    (A : Matrix Bool Bool L) (u v : Bool) :
    (((X : Matrix Bool Bool L) * A * (X : Matrix Bool Bool L)) : Matrix Bool Bool L) u v =
      A (!u) (!v) := by
  cases u <;> cases v <;> simp [Matrix.mul_apply,X,Signature.disequality]

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

abbrev sourceComplex : OI.K G →+* ℂ := ClosurePhysicalBridge.complexEmbedding G

def mapPresentation {n : ℕ} (M : Presentation (OI.K G) (Fin n)) : Presentation ℂ (Fin n) where
  edges := M.edges
  ports := M.ports
  matrix := fun e => (M.matrix e).map (sourceComplex G)
  scalar := sourceComplex G M.scalar

theorem mapPresentation_tensor {n : ℕ} (M : Presentation (OI.K G) (Fin n)) :
    (mapPresentation G M).tensor = RH.mapSignature (sourceComplex G) M.tensor := by
  funext x
  simp only [mapPresentation,Presentation.tensor,productValue,RH.mapSignature,
    Matrix.map_apply,map_mul,map_prod]

/-- CURRENT safe factors are actual source binaries up to ORIGINAL-field
nonzero scale. Their normalized root condition follows from the actual group. -/
theorem current_safe_root (B : Binary (K:=OI.K G))
    (safe : SafeBinary (actualTransfers P.family) B) :
    IsRootMonomial N.m (B.map (sourceComplex G)) := by
  have hs : ∃ C : Binary (K:=OI.K G), ActualNonsingular P.family C ∧
      ∃ c : OI.K G, c ≠ 0 ∧ transfer B = c • transfer C := safe
  obtain ⟨C,actual,c,hc,hT⟩ := hs
  have hB : B = c • C := by
    have hh := congrArg (fun T : Binary (K:=OI.K G) => T * X) hT
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using hh
  have hr := groupM_complex_root (by have := N.range; omega)
    (C.map (ClosureSourceRows.embedding G))
    (ClosureSourceRows.actual_binary_groupM G P torsion N C actual)
  have he : B.map (sourceComplex G) = sourceComplex G c •
      complexMatrix (C.map (ClosureSourceRows.embedding G)) := by
    rw [hB]
    funext u v
    simp only [Matrix.map_apply,Pi.smul_apply,smul_eq_mul,map_mul,
      sourceComplex,ClosurePhysicalBridge.complexEmbedding,
      ClosurePhysicalBridge.algebraicEmbedding,ClosureSourceRows.embedding,
      complexMatrix,RingHom.comp_apply]
    rfl
  rw [he]
  exact (rootMonomial_smul_iff N.m _ ((map_ne_zero _).mpr hc) _).mpr hr

theorem current_matching_map {n : ℕ} (f : Signature (OI.K G) n)
    (matching : MatchingOrZero (actualTransfers P.family) f) :
    RH.mapSignature (sourceComplex G) f = 0 ∨
      RootMatching N.m (RH.mapSignature (sourceComplex G) f) := by
  rcases matching with rfl | ⟨M,valid,scalar,rfl⟩
  · left; funext x; exact map_zero _
  · right
    refine ⟨mapPresentation G M,fun e => current_safe_root G P torsion N _ (valid e),
      (map_ne_zero _).mpr scalar,(mapPresentation_tensor G M).symm⟩

/-- Exact analytic root chosen inside AlgebraicComplex. The even raw-X
sandwich uses the INVERSE phase; the odd sandwich uses the phase itself. -/
def cardPhase (p : Bool) (t : ℂ) (ht : t^N.m=1) : Phase N.m :=
  CyclicBoundary.AlgebraicRepresentatives.liftRoot (by have := N.range; omega)
    ⟨if p then t else t⁻¹,by cases p <;> simp [ht,inv_pow]⟩

theorem cardPhase_value (p : Bool) (t : ℂ) (ht : t^N.m=1) :
    ((cardPhase G P torsion N p t ht).val : ℂ) = if p then t else t⁻¹ := rfl

def cardIndex (p : Bool) (t : ℂ) (ht : t^N.m=1) :=
  ClosureSourceRows.monomialIndex G P torsion N p (cardPhase G P torsion N p t ht)

def cardScalar (p : Bool) (t : ℂ) (ht : t^N.m=1) : ℂ :=
  sourceComplex G (cardIndex G P torsion N p t ht).coefficient * (if p then 1 else t⁻¹)

theorem cardScalar_nonzero (p : Bool) (t : ℂ) (ht : t^N.m=1) :
    cardScalar G P torsion N p t ht ≠ 0 := by
  have ht0 : t ≠ 0 := by intro hz; have := N.range; simp [hz,Nat.ne_of_gt (by omega : 0<N.m)] at ht
  exact mul_ne_zero ((map_ne_zero _).mpr (cardIndex G P torsion N p t ht).nonzero)
    (by cases p <;> simp [ht0])

theorem cardKernel_exact (p : Bool) (t : ℂ) (ht : t^N.m=1) :
    (X * actualRepresentative P.family torsion (cardIndex G P torsion N p t ht).key * X).map
      (sourceComplex G) = cardScalar G P torsion N p t ht •
        Holant.Dihedral.EndpointParallelogram.phaseKernel p t := by
  have normal := congrArg complexMatrix (cardIndex G P torsion N p t ht).normal
  have ht0 : t ≠ 0 := by intro hz; have := N.range; simp [hz,Nat.ne_of_gt (by omega : 0<N.m)] at ht
  have entries (u v : Bool) :
      sourceComplex G (actualRepresentative P.family torsion
        (cardIndex G P torsion N p t ht).key u v) =
      sourceComplex G (cardIndex G P torsion N p t ht).coefficient *
        complexMatrix (EqualityQuaternary.standard p (cardPhase G P torsion N p t ht).val) u v := by
    exact congrFun (congrFun normal u) v
  funext u v
  simp only [Matrix.map_apply,matrix_Xsandwich,entries]
  cases p <;> cases u <;> cases v <;>
    simp [cardScalar,complexMatrix,EqualityQuaternary.standard,R,S,diagonalKernel,Kernel.mul_apply,Signature.disequality,
      Holant.Dihedral.EndpointParallelogram.phaseKernel,cardPhase_value,ht0]

set_option maxHeartbeats 400000 in
/-- Literal no-dressing key and exact scalar for this actual CURRENT card. -/
theorem current_card_raw_scalar (h : Signature (OI.K G) 6)
    (e : Equiv.Perm (Fin 6)) (p : Bool) (t : ℂ) (ht : t^N.m=1) :
    RH.mapSignature (sourceComplex G)
      (rawCard P.family torsion h (DeckContraction.orderedKey P.family torsion e
        (cardIndex G P torsion N p t ht).key)) =
      cardScalar G P torsion N p t ht • phaseCard (RH.mapSignature (sourceComplex G) h) e p t := by
  rw [DeckContraction.rawCard_ordered,phaseCard_actual]
  have kernel := cardKernel_exact G P torsion N p t ht
  funext x
  simp only [RH.mapSignature,Signature.contract,Tensor.reindex,map_sum,map_mul,
    Pi.smul_apply,smul_eq_mul,Holant.Dihedral.EndpointParallelogram.card,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  have hk := congrFun (congrFun kernel u) v
  simp only [Matrix.map_apply,Pi.smul_apply,smul_eq_mul] at hk
  rw [hk]
  ring

/-- Actual CURRENT rawDeck stability supplies the entire ordered complex
root deck, including zero cards, with no new analytic-card premise. -/
theorem orderedRootDeck_of_current (h : Signature (OI.K G) 6)
    (stable : ∀ g ∈ rawDeck P.family torsion h,
      MatchingOrZero (actualTransfers P.family) g) :
    OrderedRootDeck N.m (RH.mapSignature (sourceComplex G) h) := by
  intro e p t ht
  have raw := stable _ (Or.inr ⟨DeckContraction.orderedKey P.family torsion e
    (cardIndex G P torsion N p t ht).key,rfl⟩)
  have mapped := current_matching_map G P torsion N _ raw
  rw [current_card_raw_scalar G P torsion N h e p t ht] at mapped
  exact rootMatchingOrZero_unscale _ (cardScalar_nonzero G P torsion N p t ht) mapped

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
