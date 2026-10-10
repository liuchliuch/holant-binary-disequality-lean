import Holant.Proofs.Closure.ClosureSourceRowsC2Deck
import Holant.Proofs.Closure.ClosureMarkedDihedral

/-! Actual retained monomial rows for the constructed native-M group branch.
Every Bool/root phase selects an ORIGINAL complete-group key. Its normalizing
scalar is recovered from a literal source entry, so it belongs to OI.K G;
normalized standard matrices are never asserted to be source gadgets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Marked Holant.Marked.SupportAtlas
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM (ClosureMarkedDihedral.Source.group (embedding G) P.family torsion))

structure MonomialIndex (p : Bool) (t : Phase N.m) where
  key : completeGroup P.family torsion
  coefficient : OI.K G
  nonzero : coefficient ≠ 0
  normal : representative G P torsion key =
    scale (embedding G coefficient) (EqualityQuaternary.standard p t.val)

/-- The analytic scalar is recovered from the fixed unit entry of the actual
ordered source matrix, not assumed to have a source-field preimage. -/
def monomialIndex (p : Bool) (t : Phase N.m) : MonomialIndex G P torsion N p t := by
  let hs := ClosureMarkedDihedral.Source.standard_source_representative
    (embedding G) P.family torsion N P.equality p t.val t.property
  let j := Classical.choose hs
  let hd := Classical.choose_spec hs
  let d := Classical.choose hd
  have hn := (Classical.choose_spec hd).1
  have he := (Classical.choose_spec hd).2
  let c := actualRepresentative P.family torsion j p false
  have hpivot : ClosureMarkedDihedral.standard p t.val p false = 1 := by
    cases p <;> simp [ClosureMarkedDihedral.standard,S,R,diagonalKernel,Kernel.mul_apply,Signature.disequality]
  have hc : embedding G c = d := by
    have h := congrFun (congrFun he p) false
    simpa only [Matrix.map_apply,scale,hpivot,mul_one] using h
  have hc0 : c ≠ 0 := by
    apply (map_ne_zero (embedding G)).mp
    rw [hc]
    exact hn
  refine ⟨j,c,hc0,?_⟩
  change Matrix.map (actualRepresentative P.family torsion j) (embedding G) = _
  rw [hc]
  exact he

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

def monomialRepresentatives : EqualityQuaternary.MonomialRepresentatives
    (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num))) N.m where
  matrix := fun p t => representative G P torsion (monomialIndex G P torsion N p t).key
  multiplier := fun p t => embedding G (monomialIndex G P torsion N p t).coefficient
  multiplier_ne_zero := fun p t => (map_ne_zero (embedding G)).mpr (monomialIndex G P torsion N p t).nonzero
  actual := fun p t => Gadget.realizes_of_mem _ .disequality _
    (representative_ambient_retained G P torsion q core hcore (by norm_num)
      (monomialIndex G P torsion N p t).key)
  normal_form := fun p t => (monomialIndex G P torsion N p t).normal

theorem monomial_retained : EqualityQuaternary.SourceRetained (.monomial N.m)
    (monomialRepresentatives G P torsion N q core hcore) :=
  fun p t => representative_ambient_retained G P torsion q core hcore (by norm_num)
    (monomialIndex G P torsion N p t).key

/-- The native-X right factor stays in the literal monomial group. Thus
binary membership, not only sparsity, follows from actual transfer membership. -/
theorem actual_binary_groupM (B : Binary (K:=OI.K G)) (hB : ActualNonsingular P.family B) :
    B.map (embedding G) ∈ groupM N.m := by
  have hm : 0 < N.m := by have := N.range; omega
  have hx : (Signature.disequality : Kernel Scalar) ∈ groupM N.m := by
    refine ⟨1,Roots.one _,Or.inr ⟨1,one_ne_zero,?_⟩⟩
    funext a b
    simp [S,R_one,Kernel.mul_equality,scale]
  have ht := ClosureMarkedDihedral.Source.actual_transfer (embedding G) P.family torsion N B hB
  have he : (transfer B).map (embedding G) = Kernel.mul (B.map (embedding G)) Signature.disequality := by
    funext a b
    cases a <;> cases b <;>
      simp [transfer,Matrix.map_apply,Matrix.mul_apply,X,Kernel.mul_apply,Signature.disequality]
  rw [he] at ht
  have h := (groupM_is_group hm).mul_mem _ ht _ hx
  rwa [Kernel.mul_assoc,Kernel.disequality_mul_disequality,Kernel.mul_equality] at h

/-- Cover arbitrary actual current binaries by the actual retained row
representatives, restoring both nonzero recorded scales. -/
theorem actual_monomial_line (B : Binary (K:=OI.K G)) (hB : ActualNonsingular P.family B) :
    EqualityQuaternary.ActualMonomialLine (monomialRepresentatives G P torsion N q core hcore)
      (B.map (embedding G)) := by
  rcases actual_binary_groupM G P torsion N B hB with ⟨t,ht,hl | hl⟩
  · obtain ⟨c,hc,he⟩ := hl
    let phase : Phase N.m := ⟨t,ht⟩
    let μ := embedding G (monomialIndex G P torsion N false phase).coefficient
    have hμ : μ ≠ 0 := (map_ne_zero (embedding G)).mpr (monomialIndex G P torsion N false phase).nonzero
    refine ⟨false,phase,c/μ,div_ne_zero hc hμ,?_⟩
    change B.map (embedding G) = scale (c/μ)
      (representative G P torsion (monomialIndex G P torsion N false phase).key)
    rw [(monomialIndex G P torsion N false phase).normal,he]
    funext a b
    change c * R t a b = (c/μ) * (μ * R t a b)
    field_simp
  · obtain ⟨c,hc,he⟩ := hl
    let phase : Phase N.m := ⟨t,ht⟩
    let μ := embedding G (monomialIndex G P torsion N true phase).coefficient
    have hμ : μ ≠ 0 := (map_ne_zero (embedding G)).mpr (monomialIndex G P torsion N true phase).nonzero
    refine ⟨true,phase,c/μ,div_ne_zero hc hμ,?_⟩
    change B.map (embedding G) = scale (c/μ)
      (representative G P torsion (monomialIndex G P torsion N true phase).key)
    rw [(monomialIndex G P torsion N true phase).normal,he]
    funext a b
    change c * S t a b = (c/μ) * (μ * S t a b)
    field_simp

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
