import Holant.Certificates.EqualityQuaternary.CoordinatePrimality
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCards
import Holant.Projective.CyclicDressing.Realization

/-! Original-field dressing through actual current group representatives.
Every coefficient multiplier is retained; all splices use native X wires. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralDressing
open Holant Holant.Tractable Holant.OpenNetworkComposition Holant.Algebraic Holant.Projective.BoundedTorsion
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry
open ClosureMarkedDihedral.Source
open scoped BigOperators Matrix
variable {L : Type*} [Field L]

theorem splice_action (φ : L →+* AlgebraicComplex) (f : Signature L 4)
    (B : Binary (K:=L)) (i : Fin 4) :
    spliceTensor f (Holant.Projective.BoundedTorsion.binarySignature B) i=
      Signature.coordinateAction (fun j => if j=i then Kernel.mul B X else Signature.equality) f := by
  funext x
  apply φ.injective
  have h := congrFun (Holant.Projective.CyclicDressing.onePort_eq_splice
    (RingHomRealization.mapSignature φ f) (B.map φ) i) x
  have hcoeff (j : Fin 4) (u v : Bool) :
      φ ((if j=i then Kernel.mul B X else Signature.equality) u v) =
      (if j=i then Kernel.mul (B.map φ) Signature.disequality else Signature.equality) u v := by
    by_cases hj : j=i <;> cases u <;> cases v <;>
      simp [hj,Kernel.mul_apply,X,Matrix.of_apply,Matrix.map_apply,
        Signature.equality,Signature.disequality,map_add,map_mul]
  have ha : φ (Signature.coordinateAction
      (fun j => if j=i then Kernel.mul B X else Signature.equality) f x) =
      Holant.Projective.CyclicDressing.onePort (RingHomRealization.mapSignature φ f)
        i (B.map φ) x := by
    simp only [Signature.coordinateAction,Holant.Projective.CyclicDressing.onePort,
      RingHomRealization.mapSignature,map_sum,map_mul,map_prod]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact hcoeff j (x j) (y j)
  have hs : φ (spliceTensor f (Holant.Projective.BoundedTorsion.binarySignature B) i x) =
      spliceTensor (RingHomRealization.mapSignature φ f)
        (kernelSignature (B.map φ)) i x := by
    simp [spliceTensor,Holant.Projective.BoundedTorsion.binarySignature,kernelSignature,
      RingHomRealization.mapSignature,Matrix.map_apply,Signature.disequality,map_sum,map_mul,map_add]
  exact hs.trans (h.symm.trans ha.symm)


theorem map_action {K M : Type*} [CommSemiring K] [CommSemiring M]
    (ρ : K→+*M) {n : ℕ} (A : Fin n→Kernel K) (q : Signature K n) :
    RingHomRealization.mapSignature ρ (Signature.coordinateAction A q)=
      Signature.coordinateAction (fun i u v=>ρ (A i u v)) (RingHomRealization.mapSignature ρ q) := by
  funext x
  simp only [RingHomRealization.mapSignature,Signature.coordinateAction,map_sum,map_mul,map_prod]

theorem action_slot_scalars {K : Type*} [CommSemiring K] {n : ℕ}
    (A : Fin n→Kernel K) (c : Fin n→K) (q : Signature K n) :
    Signature.coordinateAction (fun i=>c i • A i) q=
      (∏ i,c i) • Signature.coordinateAction A q := by
  funext x
  simp [Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,
    Finset.prod_mul_distrib,Finset.mul_sum,mul_assoc]

def fourDressing (q : Signature L 4) (B : Fin 4→Binary (K:=L)) : Signature L 4 :=
  spliceTensor (spliceTensor (spliceTensor (spliceTensor q
    (Holant.Projective.BoundedTorsion.binarySignature (B 0)) 0)
    (Holant.Projective.BoundedTorsion.binarySignature (B 1)) 1)
    (Holant.Projective.BoundedTorsion.binarySignature (B 2)) 2)
    (Holant.Projective.BoundedTorsion.binarySignature (B 3)) 3

theorem fourDressing_actual (F : SignatureFamily L) (q : Signature L 4)
    (B : Fin 4→Binary (K:=L)) (hq : Gadget.Realizes F .disequality q)
    (hB : ∀i,Gadget.Realizes F .disequality (Holant.Projective.BoundedTorsion.binarySignature (B i))) :
    Gadget.Realizes F .disequality (fourDressing q B) := by
  have h0 := realizes_splice F q _ hq (hB 0) (0 : Fin 4)
  have h1 := realizes_splice F _ _ h0 (hB 1) (1 : Fin 4)
  have h2 := realizes_splice F _ _ h1 (hB 2) (2 : Fin 4)
  exact realizes_splice F _ _ h2 (hB 3) (3 : Fin 4)

theorem fourDressing_action (φ : L→+*AlgebraicComplex) (q : Signature L 4)
    (B : Fin 4→Binary (K:=L)) : fourDressing q B=
      Signature.coordinateAction (fun i=>Kernel.mul (B i) X) q := by
  rw [fourDressing,splice_action φ,splice_action φ,splice_action φ,splice_action φ,
    Signature.coordinateAction_comp,Signature.coordinateAction_comp,Signature.coordinateAction_comp]
  congr 1
  funext j
  fin_cases j <;> simp [Kernel.equality_mul,Kernel.mul_equality]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)
variable (f : Form)
variable (model : group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group f)
abbrev OriginalIndex := completeGroup P.family tau
abbrev originalBinary (r : OriginalIndex G P tau) := actualRepresentative P.family tau r
abbrev ψ := complexEmbedding (ClosureSourceRows.embedding G)
def legSlots (r : Fin 4→OriginalIndex G P tau) (reverse : Fin 4→Bool) :=
  fun i=>some (r i,reverse i)
def originalDressed (q : Signature (OI.K G) 4) (r : Fin 4→OriginalIndex G P tau)
    (reverse : Fin 4→Bool) : Signature (OI.K G) 4 :=
  fourDressing q (fun i=>orientBinary (reverse i) (originalBinary G P tau (r i)))
def effectiveSlots (r : Fin 4→OriginalIndex G P tau) (reverse : Fin 4→Bool) :
    Fin 4→Matrix Bool Bool ℂ := fun i=>
  (orientBinary (reverse i) (originalBinary G P tau (r i))).map (ψ G)*
    Holant.Certificates.MatchingContractionClosure.X
def targetSlots (code : Fin 4→Fin 24) (reverse : Fin 4→Bool) : Fin 4→Matrix Bool Bool ℂ :=
  fun i=>if reverse i then (Preserver.kernel f (code i)).transpose else Preserver.kernel f (code i)

theorem original_dressed_action (q : Signature (OI.K G) 4)
    (r : Fin 4→OriginalIndex G P tau) (reverse : Fin 4→Bool) :
    originalDressed G P tau q r reverse=Signature.coordinateAction (fun i=>
      Kernel.mul (orientBinary (reverse i) (originalBinary G P tau (r i)))
        Holant.Certificates.MatchingContractionClosure.X) q :=
  fourDressing_action (ClosureSourceRows.embedding G) q _

theorem originalDressed_actual (q : Signature (OI.K G) 4)
    (r : Fin 4→OriginalIndex G P tau) (reverse : Fin 4→Bool)
    (hq : Gadget.Realizes P.family .disequality q) :
    Gadget.Realizes P.family .disequality (originalDressed G P tau q r reverse) :=
  fourDressing_actual P.family q _ hq
    (fun i=>realizes_orientBinary (actualRepresentative_actual P.family tau (r i)).1 (reverse i))

theorem mapped_dressed (q : Signature (OI.K G) 4) (r : Fin 4→OriginalIndex G P tau)
    (reverse : Fin 4→Bool) :
    RingHomRealization.mapSignature (ψ G) (originalDressed G P tau q r reverse)=
      Signature.coordinateAction (effectiveSlots G P tau r reverse) (RingHomRealization.mapSignature (ψ G) q) := by
  rw [original_dressed_action G P tau,map_action]
  congr 1
  funext i u v
  cases u <;> cases v <;>
    simp [effectiveSlots,Kernel.mul,Matrix.mul_apply,Matrix.map_apply,Fintype.sum_bool,
      Holant.Certificates.MatchingContractionClosure.X,Signature.disequality,map_sum,map_mul]

include model in
theorem actual_legs (code : Fin 4→Fin 24) (reverse : Fin 4→Bool) :
    ∃ r : Fin 4→OriginalIndex G P tau,∃ c : Fin 4→ℂ,
      (∀i,c i≠0) ∧ ∀i,
      (orientBinary (reverse i) (originalBinary G P tau (r i))).map (ψ G)=c i •
        (targetSlots f code reverse i*Holant.Certificates.MatchingContractionClosure.X) := by
  have h (i : Fin 4) : ∃ r : OriginalIndex G P tau,∃ c : ℂ,c≠0 ∧
      (orientBinary (reverse i) (originalBinary G P tau r)).map (ψ G)=c •
        (targetSlots f code reverse i*Holant.Certificates.MatchingContractionClosure.X) := by
    cases hr : reverse i with
    | false =>
      obtain ⟨r,c,hc,he⟩ := GlobalCloseCompletionOctahedralCards.kernel_alignment
        (ClosureSourceRows.embedding G) P.family tau f model
        (Holant.Certificates.MatchingContractionClosure.X*Preserver.kernel f (code i))
        (direction_mul (direction_X f) (Direction.standard f (code i)))
      refine ⟨r,c,hc,?_⟩
      simpa only [orientBinary,hr,Bool.false_eq_true,ite_false,targetSlots,nativePair,originalBinary,ψ,
        ←Matrix.mul_assoc,X_mul_X,Matrix.one_mul] using he
    | true =>
      obtain ⟨r,c,hc,he⟩ := GlobalCloseCompletionOctahedralCards.kernel_alignment
        (ClosureSourceRows.embedding G) P.family tau f model
        (Preserver.kernel f (code i)*Holant.Certificates.MatchingContractionClosure.X)
        (direction_mul (Direction.standard f (code i)) (direction_X f))
      have hh := congrArg Matrix.transpose he
      refine ⟨r,c,hc,?_⟩
      simpa only [orientBinary,hr,ite_true,targetSlots,nativePair,originalBinary,ψ,Matrix.transpose_map,Matrix.mul_assoc,
        X_mul_X,Matrix.mul_one,Matrix.transpose_mul,transpose_X,Matrix.transpose_smul] using hh
  choose r c hc he using h
  exact ⟨r,c,hc,he⟩

include model in
theorem actual_tensor_transport (q : Signature (OI.K G) 4)
    (code : Fin 4→Fin 24) (reverse : Fin 4→Bool) :
    ∃ r : Fin 4→OriginalIndex G P tau,∃ c : Fin 4→ℂ,(∀i,c i≠0) ∧
      RingHomRealization.mapSignature (ψ G) (originalDressed G P tau q r reverse)=
        (∏i,c i) • Signature.coordinateAction (targetSlots f code reverse) (RingHomRealization.mapSignature (ψ G) q) ∧
      (Gadget.Realizes P.family .disequality q →
        Gadget.Realizes P.family .disequality (originalDressed G P tau q r reverse)) := by
  obtain ⟨r,c,hc,he⟩ := actual_legs G P tau f model code reverse
  refine ⟨r,c,hc,?_,fun hq=>originalDressed_actual G P tau q r reverse hq⟩
  rw [mapped_dressed G P tau]
  have hs : effectiveSlots G P tau r reverse=fun i=>c i • targetSlots f code reverse i := by
    funext i
    simp only [effectiveSlots,he i,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one]
  rw [hs,action_slot_scalars]


abbrev mappedSignature (q : Signature (OI.K G) 4) :=
  RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q

def savedSlot (r : Fin 4→OriginalIndex G P tau) (reverse : Fin 4→Bool)
    (i : Fin 4) : Matrix Bool Bool AlgebraicComplex :=
  (orientBinary (reverse i) (originalBinary G P tau (r i))).map (ClosureSourceRows.embedding G)*
    Holant.Certificates.MatchingContractionClosure.X

theorem savedSlot_det (r : Fin 4→OriginalIndex G P tau) (reverse : Fin 4→Bool)
    (i : Fin 4) : (savedSlot G P tau r reverse i).det≠0 := by
  have hb : (originalBinary G P tau (r i)).det≠0 :=
    (actualRepresentative_actual P.family tau (r i)).2
  have ho : (orientBinary (reverse i) (originalBinary G P tau (r i))).det≠0 := by
    cases h : reverse i <;> simpa [orientBinary,h,Matrix.det_transpose] using hb
  have hm : ((orientBinary (reverse i) (originalBinary G P tau (r i))).map
      (ClosureSourceRows.embedding G)).det≠0 := by
    change ((ClosureSourceRows.embedding G).mapMatrix
      (orientBinary (reverse i) (originalBinary G P tau (r i)))).det≠0
    rw [←RingHom.map_det]
    exact (map_ne_zero (ClosureSourceRows.embedding G)).mpr ho
  have hx : (Holant.Certificates.MatchingContractionClosure.X :
      Matrix Bool Bool AlgebraicComplex).det≠0 := by
    have h := congrArg Matrix.det
      (Holant.Certificates.MatchingContractionClosure.X_mul_X (K:=AlgebraicComplex))
    rw [Matrix.det_mul,Matrix.det_one] at h
    intro hz
    rw [hz,zero_mul] at h
    exact zero_ne_one h
  rw [savedSlot,Matrix.det_mul]
  exact mul_ne_zero hm hx

def savedInverse (r : Fin 4→OriginalIndex G P tau) (reverse : Fin 4→Bool)
    (i : Fin 4) : Matrix Bool Bool AlgebraicComplex :=
  (savedSlot G P tau r reverse i)⁻¹

theorem savedSlot_left_inverse (r : Fin 4→OriginalIndex G P tau)
    (reverse : Fin 4→Bool) (i : Fin 4) :
    Kernel.mul (savedInverse G P tau r reverse i) (savedSlot G P tau r reverse i)=
      Signature.equality := by
  have h := Matrix.nonsing_inv_mul (savedSlot G P tau r reverse i)
    (isUnit_iff_ne_zero.mpr (savedSlot_det G P tau r reverse i))
  funext u v
  have hh := congrFun (congrFun h u) v
  simpa [savedInverse,Kernel.mul_apply,Matrix.mul_apply,Fintype.sum_bool,Matrix.one_apply,
    Signature.equality,add_comm] using hh


theorem mapped_dressing (q : Signature (OI.K G) 4)
    (r : Fin 4→OriginalIndex G P tau) (reverse : Fin 4→Bool) :
    mappedSignature G (originalDressed G P tau q r reverse)=
      Signature.coordinateAction (savedSlot G P tau r reverse) (mappedSignature G q) := by
  unfold mappedSignature
  rw [original_dressed_action G P tau,map_action]
  congr 1
  funext i u v
  cases u <;> cases v <;>
    simp [savedSlot,Kernel.mul,Matrix.mul_apply,Matrix.map_apply,Fintype.sum_bool,
      Holant.Certificates.MatchingContractionClosure.X,Signature.disequality,map_sum,map_mul]

theorem dressing_prime (q : Signature (OI.K G) 4)
    (r : Fin 4→OriginalIndex G P tau) (reverse : Fin 4→Bool)
    (hp : EqualityQuaternary.TensorPrime (mappedSignature G q)) :
    EqualityQuaternary.TensorPrime (mappedSignature G (originalDressed G P tau q r reverse)) := by
  rw [mapped_dressing G P tau]
  exact EqualityQuaternary.prime_coordinateAction hp (savedSlot G P tau r reverse)
    (savedInverse G P tau r reverse) (savedSlot_left_inverse G P tau r reverse)

structure Tensor (G : (i : Fin s)→Signature AlgebraicComplex (a i.val)) (P : Palette G) where
  table : Signature (OI.K G) 4
  actual : Gadget.Realizes P.family .disequality table
  prime : EqualityQuaternary.TensorPrime (mappedSignature G table)

include model in
theorem transport_slots (Q : Tensor G P) (code : Fin 4→Fin 24) (reverse : Fin 4→Bool)
    (slots : Fin 4→Matrix Bool Bool ℂ) (scale : Fin 4→ℂ)
    (nonzero : ∀i,scale i≠0)
    (same : slots=fun i=>scale i • targetSlots f code reverse i) :
    ∃ R : Tensor G P,∃ c : ℂ,c≠0 ∧ RingHomRealization.mapSignature (ψ G) R.table=
      c • Signature.coordinateAction slots (RingHomRealization.mapSignature (ψ G) Q.table) := by
  obtain ⟨r,d,hd,hm,ha⟩ := actual_tensor_transport G P tau f model Q.table code reverse
  have hs : (∏i,scale i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>nonzero i)
  have hds : (∏i,d i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hd i)
  refine ⟨⟨originalDressed G P tau Q.table r reverse,ha Q.actual,
    dressing_prime G P tau Q.table r reverse Q.prime⟩,(∏i,d i)/(∏i,scale i),div_ne_zero hds hs,?_⟩
  change RingHomRealization.mapSignature (ψ G) (originalDressed G P tau Q.table r reverse)=_
  rw [hm,same,action_slot_scalars,smul_smul,div_mul_cancel₀ _ hs]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralDressing
end
