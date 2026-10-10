import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseRepresentatives

/-! A bad normalized B binary is backed by an original-field singular graph.
Its actual nonzero projective coefficient, normalized parity, original graph
and current/original-G access are retained without calling it hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDenseEscape
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace R
export GlobalCloseCompletionBDenseRepresentatives (family)
end R
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

structure SingularReceipt : Type 1 where
  original : Binary (K:=OI.K G)
  nonzero : original≠0
  singular : Matrix.det original=0
  actual : Gadget.Realizes P.family .disequality (binarySignature original)
  access : CurrentSignatureAccess G P ⟨2,binarySignature original⟩
  normalized : Mat
  normalized_nonzero : normalized≠0
  normalized_parity : EightVertexGaugeParity.BinaryParity normalized
  normalized_actual : Gadget.Realizes (R.family G P) .disequality (kernelSignature normalized)
  rotation_order : ℕ
  outside : normalized∉groupM rotation_order
  coefficient : AlgebraicComplex
  coefficient_nonzero : coefficient≠0
  normalization : transport basisB (original.map (ClosureSourceRows.embedding G))=
    scale coefficient normalized

private def restored (B : Mat) : Mat :=
  Kernel.mul (Kernel.mul basisB.matrix B) (Kernel.transpose basisB.matrix)

include torsion N in
theorem original_singular (B : Mat) (nonzero : B≠0) (outside : B∉groupM N.selected.m)
    (actual : Gadget.Realizes (R.family G P) .disequality (kernelSignature B))
    (parity : EightVertexGaugeParity.BinaryParity B) : Nonempty (SingularReceipt G P) := by
  have backward := GlobalCloseCompletionBCoordinateRealizes.backward
    (ClosureSourceRows.ambientFamily G P) (StableDenseGaugeCurrent.ambient_identity G P)
    (kernelSignature B) actual
  have action : basisB.action (kernelSignature B)=kernelSignature (restored B) :=
    coordinateAction_kernelSignature basisB.matrix B
  rw [action] at backward
  obtain ⟨c,hc,hactual⟩ := backward
  have ha : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
      (kernelSignature (scale c (restored B))) := hactual
  obtain ⟨C,hC,hmap⟩ := StableDenseGaugeCurrent.binary_descends G P (scale c (restored B)) ha
  have normalized : transport basisB (C.map (ClosureSourceRows.embedding G))=scale c B := by
    rw [hmap]
    unfold transport
    rw [scale_mul_right,scale_mul_left]
    change scale c (transport basisB (restored B))=_
    rw [restored,transport_forward]
  have hn : C≠0 := by
    intro hz
    apply nonzero
    funext b d
    have h := congrFun (congrFun normalized b) d
    rw [hz] at h
    simpa [transport,Matrix.map_apply,Kernel.mul_apply,scale,hc] using h.symm
  have singular : Matrix.det C=0 := by
    by_contra hd
    have member := ClosureMarkedDihedralCoordinates.Source.actual_sector_spectrum basisB
      (ClosureSourceRows.embedding G) P.family torsion N.selected C ⟨hC,hd⟩
    rw [←transport_mul_edge,normalized,ClosureBStable.edge_exact,scale_mul_left,
      scale_mul_right,Kernel.mul_equality] at member
    have hi := (groupM_is_group (by have := N.selected.range; omega)).scale_mem _ member
      (c*ClosureBStable.edgeScalar)⁻¹ (inv_ne_zero (mul_ne_zero hc ClosureBStable.edgeScalar_nonzero))
    apply outside
    convert hi using 1
    funext b d
    simp only [scale]
    field_simp [hc,ClosureBStable.edgeScalar_nonzero]
  exact ⟨⟨C,hn,singular,hC,currentSignatureAccess G P ⟨2,binarySignature C⟩ hC,
    B,nonzero,parity,actual,N.selected.m,outside,c,hc,normalized⟩⟩

include torsion N in
theorem bad_original_singular (bad : EightVertexGaugeFamily.BadBinary (R.family G P) N.selected.m) :
    Nonempty (SingularReceipt G P) := by
  obtain ⟨B,hn,ho,ha,hp⟩ := bad
  exact original_singular G P torsion N B hn ho ha hp

private theorem determinant_formula {L : Type} [Field L] (M : Matrix Bool Bool L) :
    Matrix.det M=M false false*M true true-M false true*M true false := by
  rw [←Matrix.det_reindex_self finTwoEquiv.symm M,Matrix.det_fin_two]
  rfl

theorem SingularReceipt.normalized_singular (r : SingularReceipt G P) :
    Matrix.det (Matrix.of r.normalized)=0 := by
  have mapped : Matrix.det (r.original.map (ClosureSourceRows.embedding G))=0 := by
    rw [determinant_formula]
    change ClosureSourceRows.embedding G (r.original false false)*
      ClosureSourceRows.embedding G (r.original true true)-
      ClosureSourceRows.embedding G (r.original false true)*
      ClosureSourceRows.embedding G (r.original true false)=0
    rw [←map_mul,←map_mul,←map_sub,←determinant_formula,r.singular,map_zero]
  have leftzero : Matrix.det (Matrix.of (transport basisB
      (r.original.map (ClosureSourceRows.embedding G))))=0 := by
    change Matrix.det ((Matrix.of basisB.inverse * r.original.map (ClosureSourceRows.embedding G)) *
      Matrix.of (Kernel.transpose basisB.inverse))=0
    rw [Matrix.det_mul,Matrix.det_mul,mapped]
    simp
  have relation := congrArg (fun M : Mat=>Matrix.det (Matrix.of M)) r.normalization
  rw [leftzero] at relation
  have scaled : Matrix.det (Matrix.of (scale r.coefficient r.normalized))=
      r.coefficient^2*Matrix.det (Matrix.of r.normalized) := by
    rw [determinant_formula,determinant_formula]
    simp only [scale,Matrix.of_apply]
    ring
  have product := relation.trans scaled
  exact (mul_eq_zero.mp product.symm).resolve_left (pow_ne_zero 2 r.coefficient_nonzero)

theorem SingularReceipt.oneHot (r : SingularReceipt G P) :
    EightVertexGaugeParity.OneHot r.normalized :=
  EightVertexGaugeParity.singular_oneHot (Matrix.of r.normalized) r.normalized_parity
    r.normalized_nonzero (r.normalized_singular G P)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDenseEscape
end
