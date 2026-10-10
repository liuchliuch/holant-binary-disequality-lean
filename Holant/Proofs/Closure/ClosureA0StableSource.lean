import Holant.Proofs.Closure.ClosureA0StableDeck

/-! Exact original-field A0 normalization coefficients. The Hadamard matrix
and inverse are the already constructed ORIGINAL-field GL matrices; no new
coefficient field or assumed phase preimage is used. The normalized tensors
are coordinate data, with actual source card access kept separately. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))

def originalForward : Matrix Bool Bool (OI.K G) :=
  (ClosureMarkedCyclic.Source.sourceCoordinates (L:=OI.K G)).val

def originalInverse : Matrix Bool Bool (OI.K G) :=
  ((ClosureMarkedCyclic.Source.sourceCoordinates (L:=OI.K G))⁻¹).val

theorem originalForward_map : (originalForward G).map (algebraicEmbedding G)=basis.matrix := by
  have h := congrArg Units.val
    (ClosureMarkedCyclic.Source.sourceCoordinates_map (algebraicEmbedding G))
  exact h

theorem originalInverse_map : (originalInverse G).map (algebraicEmbedding G)=basis.inverse := by
  have h : Matrix.GeneralLinearGroup.map (algebraicEmbedding G)
      ((ClosureMarkedCyclic.Source.sourceCoordinates (L:=OI.K G))⁻¹)=
      (ClosureMarkedCyclic.coordinateGL basis)⁻¹ := by
    rw [map_inv,ClosureMarkedCyclic.Source.sourceCoordinates_map]
  exact congrArg Units.val h

theorem map_coordinate_action {L E : Type*} [Field L] [Field E] {n : ℕ}
    (φ : L →+* E) (A : Matrix Bool Bool L) (f : Signature L n) :
    Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature φ
      (Signature.coordinateAction (fun _ => A) f)=
      Signature.coordinateAction (fun _ => A.map φ)
        (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature φ f) := by
  funext x
  simp only [Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature,
    Signature.coordinateAction,map_sum,map_mul,map_prod,Matrix.map_apply]

def originalTransformed {n : ℕ} (f : Signature (OI.K G) n) : Signature (OI.K G) n :=
  Signature.coordinateAction (fun _ => originalInverse G) f

theorem originalTransformed_map {n : ℕ} (f : Signature (OI.K G) n) :
    RH.mapSignature (algebraicEmbedding G) (originalTransformed G f)=transformed G f := by
  rw [originalTransformed,map_coordinate_action,originalInverse_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem map_pullback {L E : Type*} [Field L] [Field E]
    (φ : L →+* E) (B A : Matrix Bool Bool L) :
    Matrix.map (Kernel.pullback B A) φ=Kernel.pullback (B.map φ) (A.map φ) := by
  funext u v
  change φ (Kernel.pullback B A u v)=Kernel.pullback (B.map φ) (A.map φ) u v
  simp [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,Matrix.map_apply,map_add,map_mul]

def originalClosing (p : Bool) (t : Phase N.selected.m) : Matrix Bool Bool (OI.K G) :=
  Kernel.pullback
    ((X : Binary (K:=OI.K G)) * actualRepresentative P.family torsion (index G P torsion N p t).key * X)
    (originalForward G)

set_option backward.isDefEq.respectTransparency false in
theorem originalClosing_map (p : Bool) (t : Phase N.selected.m) :
    (originalClosing G P torsion N p t).map (algebraicEmbedding G)=
      scale (cardScalar G P torsion N p t) (Holant.Dihedral.CompatibleClosure.M p t.val) := by
  unfold originalClosing
  rw [map_pullback,originalForward_map]
  exact closingKernel G P torsion N p t

/-- The card multiplier is a literal pivot of the ORIGINAL-field transformed
closing matrix. Even inverse-phase normalization is therefore source-valued. -/
def originalCardCoefficient (p : Bool) (t : Phase N.selected.m) : OI.K G :=
  originalClosing G P torsion N p t false p

theorem originalCardCoefficient_map (p : Bool) (t : Phase N.selected.m) :
    algebraicEmbedding G (originalCardCoefficient G P torsion N p t)=cardScalar G P torsion N p t := by
  have h := congrFun (congrFun (originalClosing_map G P torsion N p t) false) p
  cases p <;> simpa only [originalCardCoefficient,Matrix.map_apply,scale,
    Holant.Dihedral.CompatibleClosure.M,Holant.Marked.monomial,Bool.false_xor,
    reduceCtorEq,Bool.false_eq_true,ite_true,ite_false,mul_one] using h

theorem originalCardCoefficient_nonzero (p : Bool) (t : Phase N.selected.m) :
    originalCardCoefficient G P torsion N p t≠0 := by
  apply (map_ne_zero (algebraicEmbedding G)).mp
  rw [originalCardCoefficient_map]
  exact cardScalar_nonzero G P torsion N p t

/-- Exact analytic normalized card, entirely in the same original field.
This definition makes no gadget or palette-label assertion. -/
def originalRootCard {n : ℕ} (f : Signature (OI.K G) (n+2))
    (order : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.selected.m) : Signature (OI.K G) n :=
  fun x => (originalCardCoefficient G P torsion N p t)⁻¹ *
    originalTransformed G (rawCard P.family torsion f
      (DeckContraction.orderedKey P.family torsion order (index G P torsion N p t).key)) x

set_option backward.isDefEq.respectTransparency false in
theorem originalRootCard_map {n : ℕ} (f : Signature (OI.K G) (n+2))
    (order : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.selected.m) :
    RH.mapSignature (algebraicEmbedding G) (originalRootCard G P torsion N f order p t)=
      rootCard G P torsion N f order p t := by
  have mapped : RH.mapSignature (algebraicEmbedding G)
      (originalTransformed G (rawCard P.family torsion f
        (DeckContraction.orderedKey P.family torsion order (index G P torsion N p t).key)))=
      cardScalar G P torsion N p t • rootCard G P torsion N f order p t := by
    rw [originalTransformed_map]
    exact ordered_card_raw_scalar G P torsion N f order p t
  funext x
  change algebraicEmbedding G ((originalCardCoefficient G P torsion N p t)⁻¹ * _)=_
  rw [map_mul,map_inv₀,originalCardCoefficient_map]
  have h := congrFun mapped x
  simp only [RH.mapSignature,Pi.smul_apply,smul_eq_mul] at h
  rw [h]
  rw [←mul_assoc,inv_mul_cancel₀ (cardScalar_nonzero G P torsion N p t),one_mul]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
end
