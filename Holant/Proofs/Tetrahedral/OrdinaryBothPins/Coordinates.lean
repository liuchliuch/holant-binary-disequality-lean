import Holant.Proofs.Tetrahedral.OrdinaryUnaryAccess.Source


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution UniversalPairReduction
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.GeneralExtraction GeneralPowerExposure

namespace Single
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess
  (K F pin unary parent matrix_inverse action_inverse_pin action_unary action_pair
   parent_power unaryPower powerNetwork paletteArity palette palette_old palette_pin
   palette_family palette_ambient inputEncoding value source sourceOriginalL)
end Single
namespace Anchor
export Holant.LocalDrafts.MainChain.QuaternaryAnchorAccess
  (arity matrix inverse inverse_matrix kappa kappa_ne pulled_edge)
end Anchor
namespace Companion
export Holant.LocalDrafts.MainChain.QuaternaryOrdinaryCompanion
  (tables targetValue controlled decoded decoded_eq4 eq4Index)
end Companion
namespace Pair
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication
  (pinPair sourceValue controlled sourceEncoding)
end Pair

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (FiniteFamily.family G))
local instance : Algebra ℚ (Single.K G A) := (Single.K G A).algebra'
local instance : CharZero (Single.K G A) := Algebra.charZero_of_charZero ℚ (Single.K G A)

/-- Exactly the first source's public table, including all repeated old
signatures and arbitrary occurrences of its false pin. -/
abbrev old := Single.palette G A false
abbrev oldArity := Single.paletteArity G A
theorem old_table_eq : Companion.tables (Single.F G A) (old G A)=
    Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess.paletteTables G A false := rfl
theorem old_encoding_eq : RawClosedNetwork.validatedEncoding (s+2) 1 (oldArity G A)=
    Single.inputEncoding G A := rfl
theorem old_value_eq : Companion.targetValue (Single.F G A) (old G A)=Single.value G A false := rfl
def eq4Index : Fin (s+2) := ⟨s,by omega⟩
theorem old_eq4 :
    (⟨oldArity G A s,old G A (eq4Index (s:=s))⟩ : AnySignature (Single.K G A))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ :=
  (Single.palette_old G A false (Companion.eq4Index (s:=s))).trans
    (Companion.decoded_eq4 G A)

abbrev pairArity := extendedArity (s+2) (oldArity G A)
def arity (i : ℕ) : ℕ := if i<s+3 then pairArity G A i else 1
def pairFamily := BinaryFamily.signatures (old G A) (Pair.pinPair (K:=Single.K G A) true)
theorem base_arity (i : Fin (s+3)) : arity G A i.val=pairArity G A i.val := by
  simp only [arity,if_pos i.isLt]

def ordinaryTable (i : ℕ) : Signature (Single.K G A) (arity G A i) :=
  if hi : i<s+3 then
    fun x => pairFamily G A ⟨i,hi⟩
      (fun k => x (Fin.cast (base_arity G A ⟨i,hi⟩).symm k))
  else fun x => Single.pin G A true (fun k => x (Fin.cast (by simp [arity,hi]) k))
def nativeTable (i : ℕ) : Signature (Single.K G A) (arity G A i) :=
  Signature.coordinateAction (fun _ => Anchor.inverse G A) (ordinaryTable G A i)
abbrev ordinaryFamily (n : ℕ) :=
  FactorSaturation.PrefixMachine.family (s:=s+3) (ordinaryTable G A) n
abbrev nativeFamily (n : ℕ) :=
  FactorSaturation.PrefixMachine.family (s:=s+3) (nativeTable G A) n

private theorem signature_cast_sigma {K : Type*} {m n : ℕ} (h : m=n)
    (f : Signature K m) :
    (⟨n,fun x => f (fun k => x (Fin.cast h k))⟩ : AnySignature K)=⟨m,f⟩ := by
  subst n
  rfl


/-- The entire old table survives at precisely the same indices. In
particular this includes the FIRST unary, not merely the original RG rows. -/
theorem base_old (i : Fin (s+2)) :
    (⟨arity G A i.val,ordinaryFamily G A 0 ⟨i.val,by have := i.isLt; omega⟩⟩ :
      AnySignature (Single.K G A))=⟨oldArity G A i.val,old G A i⟩ := by
  have hi : i.val<s+3 := by have := i.isLt; omega
  change (⟨arity G A i.val,ordinaryTable G A i.val⟩ : AnySignature (Single.K G A))=_
  simp only [ordinaryTable,dif_pos hi]
  apply (signature_cast_sigma (base_arity G A ⟨i.val,hi⟩).symm
    (pairFamily G A ⟨i.val,hi⟩)).trans
  unfold pairFamily BinaryFamily.signatures
  simp only [Fin.val_mk,dif_pos i.isLt]
  exact signature_cast_sigma (m:=oldArity G A i.val) (n:=pairArity G A i.val)
    (by simp [pairArity,extendedArity,i.isLt]) (old G A i)

theorem base_first_pin :
    (⟨arity G A (s+1),ordinaryFamily G A 0 ⟨s+1,by omega⟩⟩ :
      AnySignature (Single.K G A))=⟨1,Single.pin G A false⟩ :=
  (base_old G A ⟨s+1,by omega⟩).trans (Single.palette_pin G A false)

theorem base_signatures :
    RawArityTransport.signatures (base_arity G A) (ordinaryFamily G A 0)=pairFamily G A := by
  funext i x
  simp [RawArityTransport.signatures,ordinaryFamily,FactorSaturation.PrefixMachine.family,
    ordinaryTable,i.isLt]

theorem forward (i : ℕ) :
    Signature.coordinateAction (fun _ => Anchor.matrix G A) (nativeTable G A i)=
      ordinaryTable G A i :=
  Signature.coordinateAction_cancel _ _ (fun _ => Single.matrix_inverse G A) _


private def nativeAny (f : AnySignature (Single.K G A)) : AnySignature (Single.K G A) :=
  ⟨f.1,Signature.coordinateAction (fun _ => Anchor.inverse G A) f.2⟩

theorem ordinary_parent_label :
    (⟨arity G A (s+2),ordinaryTable G A (s+2)⟩ : AnySignature (Single.K G A))=
      ⟨2,fun x => Pair.pinPair (K:=Single.K G A) true (x 0) (x 1)⟩ := by
  have hs : s+2<s+3 := by omega
  simp only [ordinaryTable,dif_pos hs]
  apply (signature_cast_sigma (base_arity G A ⟨s+2,hs⟩).symm
    (pairFamily G A ⟨s+2,hs⟩)).trans
  unfold pairFamily BinaryFamily.signatures
  simp only [Fin.val_mk,dif_neg (Nat.lt_irrefl (s+2))]
  exact signature_cast_sigma (m:=2) (n:=pairArity G A (s+2))
    (by simp [pairArity,extendedArity])
    (fun x => Pair.pinPair (K:=Single.K G A) true (x 0) (x 1))

theorem parent_label :
    (⟨arity G A (s+2),nativeFamily G A 0 ⟨s+2,by omega⟩⟩ :
      AnySignature (Single.K G A))=⟨2,Single.parent G A true⟩ := by
  have h := congrArg (nativeAny G A) (ordinary_parent_label G A)
  simpa only [nativeAny,Single.action_pair,nativeFamily,
    FactorSaturation.PrefixMachine.family,nativeTable] using h

def powerLabels : Labelling (Single.powerNetwork G A true).shape (s+3) 1 (arity G A) where
  vertex _ := ⟨s+2,by omega⟩
  vertex_arity _ := congrArg Sigma.fst (parent_label G A)
  edge := Fin.elim0

/-- The previously proved square corolla, with its SAME network and
ordered boundary, now addresses the pair after the retained false-pin row. -/
def unaryPower : PowerMacro (nativeFamily G A 0) (Single.unary G A true) where
  exponent := 2
  positive := by decide
  scale := 1
  scale_ne_zero := one_ne_zero
  network := Single.powerNetwork G A true
  labels := powerLabels G A
  value := by
    rw [Labelling.denote_template]
    have hn : ((powerLabels G A).sourceNetwork (nativeFamily G A 0)
        (fun _ : Fin 1 => Signature.disequality)).denote=
        (Single.powerNetwork G A true).denote := by
      apply Network.denote_congr
      · intro v x
        exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
          (nativeFamily G A 0 ⟨s+2,by omega⟩) (Single.parent G A true)
          (parent_label G A) (congrArg Sigma.fst (parent_label G A)) x
      · intro e b c
        exact Fin.elim0 e
    rw [hn]
    change (Network.corolla (Single.parent G A true)).denote = _
    rw [Network.denote_corolla,Single.parent_power]
    simp only [one_mul]

theorem ordinary_next_label :
    (⟨arity G A (s+3),ordinaryTable G A (s+3)⟩ : AnySignature (Single.K G A))=
      ⟨1,Single.pin G A true⟩ := by
  simp only [ordinaryTable,dif_neg (Nat.lt_irrefl (s+3))]
  exact signature_cast_sigma (by simp [arity]) (Single.pin G A true)

theorem next_label :
    (⟨arity G A (s+3),nativeTable G A (s+3)⟩ : AnySignature (Single.K G A))=
      ⟨1,Single.unary G A true⟩ := by
  have h := congrArg (nativeAny G A) (ordinary_next_label G A)
  simpa only [nativeAny,nativeTable,Single.action_inverse_pin] using h

def nextPower : PowerMacro (nativeFamily G A 0) (nativeTable G A (s+3)) :=
  QuaternaryUnaryAccess.castPower (next_label G A) (unaryPower G A)

theorem power_network_same : (unaryPower G A).network=(Single.unaryPower G A true).network := rfl
theorem power_exponent : (unaryPower G A).exponent=2 := rfl
theorem power_scale : (unaryPower G A).scale=1 := rfl
theorem power_ports (i : Fin 2) :
    (unaryPower G A).network.shape.ports ⟨⟨0,by change 0<1; decide⟩,i⟩=Sum.inl i := rfl

end Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins
