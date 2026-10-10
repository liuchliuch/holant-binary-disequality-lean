import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Backward
import Holant.Proofs.Closure.ClosureA0StableCards

/-! A bad normalized A0 binary is backed by an original-field singular graph.
Its actual nonzero projective coefficient, normalized parity, original graph
and current/original-G access are retained without calling it hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0DenseEscape
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace R
export GlobalCloseCompletionA0CurrentSource (family)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

structure SingularReceipt : Type 1 where
  original : Binary (K:=OI.K G)
  nonzero : original≠0
  singular : Matrix.det original=0
  actual : Gadget.Realizes P.family .disequality (binarySignature original)
  access : CurrentSignatureAccess G P ⟨2,binarySignature original⟩
  normalized : Mat
  normalized_nonzero : normalized≠0
  normalized_parity : EightVertexGaugeParity.BinaryParity normalized
  normalized_actual : Gadget.Realizes (R.family G P torsion q core literal) .disequality (kernelSignature normalized)
  rotation_order : ℕ
  outside : normalized∉groupM rotation_order
  coefficient : AlgebraicComplex
  coefficient_nonzero : coefficient≠0
  normalization : transport GlobalCloseCompletionA0Workfield.basis (original.map (ClosureSourceRows.embedding G))=
    scale coefficient normalized

private def restored (B : Mat) : Mat :=
  Kernel.mul (Kernel.mul GlobalCloseCompletionA0Workfield.basis.matrix B) (Kernel.transpose GlobalCloseCompletionA0Workfield.basis.matrix)

include N stable in
theorem original_singular (B : Mat) (nonzero : B≠0) (outside : B∉groupM N.selected.m)
    (actual : Gadget.Realizes (R.family G P torsion q core literal) .disequality (kernelSignature B))
    (parity : EightVertexGaugeParity.BinaryParity B) : Nonempty (SingularReceipt G P torsion q core literal) := by
  have backward := GlobalCloseCompletionA0Backward.backward G P torsion N q core literal stable
    (kernelSignature B) actual
  have action : GlobalCloseCompletionA0Workfield.basis.action (kernelSignature B)=kernelSignature (restored B) :=
    coordinateAction_kernelSignature GlobalCloseCompletionA0Workfield.basis.matrix B
  rw [action] at backward
  obtain ⟨c,hc,hactual⟩ := backward
  have ha : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
      (kernelSignature (scale c (restored B))) := hactual
  obtain ⟨C,hC,hmap⟩ := StableDenseGaugeCurrent.binary_descends G P (scale c (restored B)) ha
  have normalized : transport GlobalCloseCompletionA0Workfield.basis (C.map (ClosureSourceRows.embedding G))=scale c B := by
    rw [hmap]
    unfold transport
    rw [scale_mul_right,scale_mul_left]
    change scale c (transport GlobalCloseCompletionA0Workfield.basis (restored B))=_
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
    have member := ClosureA0Stable.actual_table_mem G P torsion N C ⟨hC,hd⟩
    change transport GlobalCloseCompletionA0Workfield.basis
      (C.map (ClosureSourceRows.embedding G))∈groupM N.selected.m at member
    rw [normalized] at member
    have hi := (groupM_is_group (by have := N.range; omega)).scale_mem _ member c⁻¹ (inv_ne_zero hc)
    apply outside
    convert hi using 1
    funext b d
    simp only [scale]
    field_simp [hc]
  exact ⟨⟨C,hn,singular,hC,currentSignatureAccess G P ⟨2,binarySignature C⟩ hC,
    B,nonzero,parity,actual,N.selected.m,outside,c,hc,normalized⟩⟩

include N stable in
theorem bad_original_singular (bad : EightVertexGaugeFamily.BadBinary (R.family G P torsion q core literal) N.selected.m) :
    Nonempty (SingularReceipt G P torsion q core literal) := by
  obtain ⟨B,hn,ho,ha,hp⟩ := bad
  exact original_singular G P torsion N q core literal stable B hn ho ha hp

private theorem determinant_formula {L : Type} [Field L] (M : Matrix Bool Bool L) :
    Matrix.det M=M false false*M true true-M false true*M true false := by
  rw [←Matrix.det_reindex_self finTwoEquiv.symm M,Matrix.det_fin_two]
  rfl

theorem SingularReceipt.normalized_singular (r : SingularReceipt G P torsion q core literal) :
    Matrix.det (Matrix.of r.normalized)=0 := by
  have mapped : Matrix.det (r.original.map (ClosureSourceRows.embedding G))=0 := by
    rw [determinant_formula]
    change ClosureSourceRows.embedding G (r.original false false)*
      ClosureSourceRows.embedding G (r.original true true)-
      ClosureSourceRows.embedding G (r.original false true)*
      ClosureSourceRows.embedding G (r.original true false)=0
    rw [←map_mul,←map_mul,←map_sub,←determinant_formula,r.singular,map_zero]
  have leftzero : Matrix.det (Matrix.of (transport GlobalCloseCompletionA0Workfield.basis
      (r.original.map (ClosureSourceRows.embedding G))))=0 := by
    change Matrix.det ((Matrix.of GlobalCloseCompletionA0Workfield.basis.inverse * r.original.map (ClosureSourceRows.embedding G)) *
      Matrix.of (Kernel.transpose GlobalCloseCompletionA0Workfield.basis.inverse))=0
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

theorem SingularReceipt.oneHot (r : SingularReceipt G P torsion q core literal) :
    EightVertexGaugeParity.OneHot r.normalized :=
  EightVertexGaugeParity.singular_oneHot (Matrix.of r.normalized) r.normalized_parity
    r.normalized_nonzero (r.normalized_singular G P torsion q core literal)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0DenseEscape
end
