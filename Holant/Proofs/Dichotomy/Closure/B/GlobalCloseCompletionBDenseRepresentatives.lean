import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBCoordinateRealizes
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBNativeCodec
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBQuaternary
import Holant.Proofs.Dichotomy.Closure.Dense.GlobalCloseCompletionDenseCanonicalCurrent

/-! Actual monomial representatives in the genuine normalized B alphabet.
The original physical representative is transformed by a real projective
network; its new graph coefficient and the B edge multiplier remain explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDenseRepresentatives
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas Holant.Complexity
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace Coord
export GlobalCloseCompletionBCoordinateRealizes (family identity forward backward)
end Coord
namespace Q
export GlobalCloseCompletionBQuaternary (family normalized old_mapped identity_member)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

abbrev family := Coord.family (ClosureSourceRows.ambientFamily G P)
theorem family_eq : family G P=Q.family G P := by
  ext f
  constructor
  · rintro (⟨_,⟨_,⟨i,rfl⟩,rfl⟩,rfl⟩|rfl)
    · exact ⟨GlobalCloseCompletionBOrdinarySource.oldLabel G P i,Q.old_mapped G P i⟩
    · exact Q.identity_member G P
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<P.count
    · have label : i=GlobalCloseCompletionBOrdinarySource.oldLabel G P ⟨i.val,hi⟩ := Fin.ext rfl
      rw [label]
      have member : (⟨P.arity i.val,basisB.symm.action (GlobalCloseCompletionBWorkfield.mapped G P ⟨i.val,hi⟩)⟩ :
          AnySignature AlgebraicComplex)∈family G P :=
        Or.inl ⟨_,⟨⟨P.arity i.val,P.table ⟨i.val,hi⟩⟩,⟨⟨i.val,hi⟩,rfl⟩,rfl⟩,rfl⟩
      exact Eq.mpr (congrArg (fun f : AnySignature AlgebraicComplex=>f∈family G P)
        (Q.old_mapped G P ⟨i.val,hi⟩)) member
    · have label : i=GlobalCloseCompletionBOrdinarySource.xLabel G P := by
        apply Fin.ext
        change i.val=P.count
        have := i.isLt
        omega
      rw [label]
      dsimp only
      rw [GlobalCloseCompletionBNativeSource.identity_signature]
      right
      change RingHomRealization.mapAny (GlobalCloseCompletionBWorkfield.K G P).val.toRingHom
        (⟨2,fun x=>Signature.equality (x 0) (x 1)⟩ : AnySignature (GlobalCloseCompletionBWorkfield.K G P))=
          (⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)
      apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
      funext x
      cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,kernelSignature,Signature.equality]

theorem family_finite_eq : family G P=UniversalPairReduction.FiniteFamily.family
    (GlobalCloseCompletionBNativeCodec.mapped G P) := family_eq G P

abbrev original := HistorySectorNormalized.representatives G P torsion basisB N.selected

def coefficient (p : Bool) (t : Phase N.selected.m) : AlgebraicComplex :=
  (Coord.forward (ClosureSourceRows.ambientFamily G P) (StableDenseGaugeCurrent.ambient_identity G P)
    (kernelSignature ((original G P torsion N).matrix p t)) ((original G P torsion N).actual p t)).choose

theorem coefficient_nonzero (p : Bool) (t : Phase N.selected.m) : coefficient G P torsion N p t≠0 :=
  (Coord.forward (ClosureSourceRows.ambientFamily G P) (StableDenseGaugeCurrent.ambient_identity G P)
    (kernelSignature ((original G P torsion N).matrix p t)) ((original G P torsion N).actual p t)).choose_spec.1

theorem actual (p : Bool) (t : Phase N.selected.m) : Gadget.Realizes (family G P) .disequality
    (kernelSignature (scale (coefficient G P torsion N p t)
      (transport basisB ((original G P torsion N).matrix p t)))) := by
  have h := (Coord.forward (ClosureSourceRows.ambientFamily G P) (StableDenseGaugeCurrent.ambient_identity G P)
    (kernelSignature ((original G P torsion N).matrix p t)) ((original G P torsion N).actual p t)).choose_spec.2
  change Gadget.Realizes (family G P) .disequality (fun x=>coefficient G P torsion N p t*
    basisB.symm.action (kernelSignature ((original G P torsion N).matrix p t)) x) at h
  rw [transport_signature] at h
  exact h

theorem normal (p : Bool) (t : Phase N.selected.m) :
    transport basisB ((original G P torsion N).matrix p t)=
      scale ((original G P torsion N).multiplier p t/ClosureBStable.edgeScalar) (standard p t.val) := by
  have h := (original G P torsion N).transfer p t
  rw [←transport_mul_edge,ClosureBStable.edge_exact,scale_mul_right,Kernel.mul_equality] at h
  funext b c
  have hh := congrFun (congrFun h b) c
  change ClosureBStable.edgeScalar*transport basisB ((original G P torsion N).matrix p t) b c=
    (original G P torsion N).multiplier p t*standard p t.val b c at hh
  change _=((original G P torsion N).multiplier p t/ClosureBStable.edgeScalar)*standard p t.val b c
  apply (mul_left_cancel₀ ClosureBStable.edgeScalar_nonzero)
  rw [hh]
  field_simp [ClosureBStable.edgeScalar_nonzero]

def representatives : MonomialRepresentatives (family G P) N.selected.m where
  matrix p t := scale (coefficient G P torsion N p t) (transport basisB ((original G P torsion N).matrix p t))
  multiplier p t := coefficient G P torsion N p t*((original G P torsion N).multiplier p t/ClosureBStable.edgeScalar)
  multiplier_ne_zero p t := mul_ne_zero (coefficient_nonzero G P torsion N p t)
    (div_ne_zero ((original G P torsion N).multiplier_ne_zero p t) ClosureBStable.edgeScalar_nonzero)
  actual p t := actual G P torsion N p t
  normal_form p t := by
    rw [normal]
    funext b c
    simp only [scale]
    ring

include torsion N in
theorem fullParity_or_bad (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
    (literal : core.signature=⟨4,q⟩) (p : Bool)
    (full : ∀x,Q.normalized G q x≠0 ↔ parity x=p) :
    Nonempty (GlobalCloseCompletionBDenseCanonical.Receipt (family G P) N.selected.m) ∨
      EightVertexGaugeFamily.BadBinary (family G P) N.selected.m := by
  apply GlobalCloseCompletionDenseCanonicalCurrent.fullParity_or_bad N.selected.range N.selected.omega
    N.selected.primitive (family G P) (Coord.identity _) (representatives G P torsion N)
    (Q.normalized G q) ?_ p full
  apply Gadget.realizes_of_mem
  exact Or.inl ⟨⟨4,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q⟩,
    ⟨⟨4,q⟩,literal ▸ core.retained,rfl⟩,rfl⟩

def finiteCanonical (C : GlobalCloseCompletionBDenseCanonical.Canonical (family G P)) :
    GlobalCloseCompletionBDenseCanonical.Canonical (UniversalPairReduction.FiniteFamily.family
      (GlobalCloseCompletionBNativeCodec.mapped G P)) where
  weight := C.weight
  weight_nonzero := C.weight_nonzero
  eighth := C.eighth
  root := C.root
  root_nonzero := C.root_nonzero
  square := C.square
  signature := C.signature
  actual := by rw [←family_finite_eq G P]; exact C.actual
  vertexScale := C.vertexScale
  vertex_nonzero := C.vertex_nonzero
  anchor_exact := C.anchor_exact
  binary := C.binary
  binary_actual := by rw [←family_finite_eq G P]; exact C.binary_actual
  binaryScale := C.binaryScale
  binary_nonzero := C.binary_nonzero
  binary_exact := C.binary_exact


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDenseRepresentatives
end
