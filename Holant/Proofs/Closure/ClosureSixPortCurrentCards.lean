import Holant.Proofs.Closure.ClosureSixPortCurrent

/-! NEW UNVERIFIED all-arity ORIGINAL-field native-M matching transport.
The scalar-valued presentation is literal coefficientwise transport and retains
ordered ports; no normalized table is claimed to be an actual source label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Tractable Holant.Algebraic Holant.Projective Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Marked Holant.Marked.SupportAtlas

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

def AlgebraicRootMatching {n : ℕ} (m : ℕ) (q : Signature AlgebraicComplex n) : Prop :=
  ∃ M : Presentation AlgebraicComplex (Fin n),
    (∀ e, M.matrix e ∈ groupM m) ∧ M.scalar ≠ 0 ∧ q = M.tensor

def algebraicPresentation {n : ℕ} (M : Presentation (OI.K G) (Fin n)) :
    Presentation AlgebraicComplex (Fin n) where
  edges := M.edges
  ports := M.ports
  matrix := fun e => (M.matrix e).map (ClosureSourceRows.embedding G)
  scalar := ClosureSourceRows.embedding G M.scalar

theorem algebraicPresentation_tensor {n : ℕ} (M : Presentation (OI.K G) (Fin n)) :
    (algebraicPresentation G M).tensor =
      RH.mapSignature (ClosureSourceRows.embedding G) M.tensor := by
  funext x
  simp only [algebraicPresentation,Presentation.tensor,productValue,RH.mapSignature,
    Matrix.map_apply,map_mul,map_prod]

theorem current_safe_groupM (B : Binary (K:=OI.K G))
    (safe : SafeBinary (actualTransfers P.family) B) :
    B.map (ClosureSourceRows.embedding G) ∈ groupM N.m := by
  have hs : ∃ C : Binary (K:=OI.K G), ActualNonsingular P.family C ∧
      ∃ c : OI.K G, c ≠ 0 ∧ transfer B = c • transfer C := safe
  obtain ⟨C,actual,c,hc,hT⟩ := hs
  have hB : B = c • C := by
    have hh := congrArg (fun T : Binary (K:=OI.K G) => T * X) hT
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using hh
  have actualM := ClosureSourceRows.actual_binary_groupM G P torsion N C actual
  have he : B.map (ClosureSourceRows.embedding G) =
      scale (ClosureSourceRows.embedding G c) (C.map (ClosureSourceRows.embedding G)) := by
    rw [hB]
    funext u v
    change ClosureSourceRows.embedding G (c * C u v) =
      ClosureSourceRows.embedding G c * ClosureSourceRows.embedding G (C u v)
    exact map_mul _ _ _
  rw [he]
  exact (groupM_is_group (by have := N.range; omega)).scale_mem _ actualM _ ((map_ne_zero _).mpr hc)

/-- Every CURRENT matching output, at every arity, has an exact algebraic
presentation with root-m actual-group factors and a nonzero original scalar. -/
theorem current_matching_algebraic {n : ℕ} (f : Signature (OI.K G) n)
    (matching : MatchingOrZero (actualTransfers P.family) f) :
    RH.mapSignature (ClosureSourceRows.embedding G) f = 0 ∨
      AlgebraicRootMatching N.m (RH.mapSignature (ClosureSourceRows.embedding G) f) := by
  rcases matching with rfl | ⟨M,valid,scalar,rfl⟩
  · left; funext x; exact map_zero _
  · right
    refine ⟨algebraicPresentation G M,fun e => current_safe_groupM G P torsion N _ (valid e),
      (map_ne_zero _).mpr scalar,(algebraicPresentation_tensor G M).symm⟩

/-- Any literal ordered raw key in the CURRENT deck inherits the all-arity
algebraic monomial matching presentation. -/
theorem current_rawCard_algebraic {n : ℕ} (h : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion h, MatchingOrZero (actualTransfers P.family) g)
    (key : RawCardKey n (completeGroup P.family torsion)) :
    RH.mapSignature (ClosureSourceRows.embedding G) (rawCard P.family torsion h key) = 0 ∨
      AlgebraicRootMatching N.m
        (RH.mapSignature (ClosureSourceRows.embedding G) (rawCard P.family torsion h key)) :=
  current_matching_algebraic G P torsion N _ (stable _ (Or.inr ⟨key,rfl⟩))

/-- Exact all-arity no-dressing key/scalar identity. The scalar is the SAME
one derived from the actual ORIGINAL-field representative used in the six-port bridge. -/
theorem ordered_card_raw_scalar {n : ℕ} (h : Signature (OI.K G) (n+2))
    (e : Equiv.Perm (Fin (n+2))) (p : Bool) (t : ℂ) (ht : t^N.m=1) :
    RH.mapSignature (sourceComplex G)
      (rawCard P.family torsion h (DeckContraction.orderedKey P.family torsion e
        (cardIndex G P torsion N p t ht).key)) =
      cardScalar G P torsion N p t ht •
        Holant.Dihedral.EndpointParallelogram.card (RH.mapSignature (sourceComplex G) h) e p t 1 := by
  rw [DeckContraction.rawCard_ordered]
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

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
