import Holant.Proofs.Reductions.FrozenFactorNormalization.Palette
import Holant.Proofs.Reductions.FrozenFactorNormalization.ScalarProgram


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FrozenFactorNormalization.PaletteCodec
open Holant.Tractable
open Holant.Algebraic Holant.Complexity UniversalPairReduction.Surgery
open Holant.LocalDrafts.FinitePGL2.Stabilization
open GeneralExtraction
variable {L : Type} [Field L] (φ : L →+* AlgebraicComplex)
variable {m t : ℕ} {a : ℕ → ℕ}
variable (P : Fin m → AnySignature L)
variable (H : (i : Fin t) → Signature AlgebraicComplex (a i.val))
def catalogue (i : Fin t) : AnySignature AlgebraicComplex := ⟨a i.val,H i⟩
variable (U : ∀ i, KeyLift φ (catalogue H i))

abbrev signature := Palette.signature φ P (catalogue H) U
def lookup (j : ℕ) : AnySignature L := if hj : j < m+t then signature φ P H U ⟨j,hj⟩ else ⟨0,0⟩
def arity (j : ℕ) : ℕ := (lookup φ P H U j).1
def tableL (j : Fin (m+t)) : Signature L (arity φ P H U j.val) := (lookup φ P H U j.val).2
def table (j : Fin (m+t)) : Signature AlgebraicComplex (arity φ P H U j.val) :=
  RH.mapSignature φ (tableL φ P H U j)
@[simp] theorem lookup_fin (j : Fin (m+t)) : lookup φ P H U j.val = signature φ P H U j := by
  simp [lookup,j.isLt]
theorem signature_map (j : Fin (m+t)) :
    (⟨arity φ P H U j.val,table φ P H U j⟩ : AnySignature AlgebraicComplex) =
      RH.mapAny φ (signature φ P H U j) := by
  change RH.mapAny φ (lookup φ P H U j.val) = _
  rw [lookup_fin]
theorem public_image : Set.range (fun j => (⟨arity φ P H U j.val,table φ P H U j⟩ :
    AnySignature AlgebraicComplex)) = RH.mapFamily φ (Palette.family φ P (catalogue H) U) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨_,⟨i,rfl⟩,(signature_map φ P H U i).symm⟩
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,signature_map φ P H U i⟩

def read (f : AnySignature AlgebraicComplex) (bits : List Bool) := f.2 (fun k => bits.getD k.val false)
theorem table_read (i : Fin (m+t)) (bits : List Bool) :
    Choice.table (table φ P H U) i.val bits = read (RH.mapAny φ (signature φ P H U i)) bits := by
  have he := congrArg (fun f => read f bits) (signature_map φ P H U i)
  simpa [Choice.table,i.isLt,read] using he

variable (hn : ∀ i, H i ≠ 0) (ρ : Fin m → Fin t)
variable (hP : ∀ i, RH.mapAny φ (P i) = catalogue H (ρ i))
def forwardArity (i : Fin (m+t)) : a (Palette.target ρ i).val = arity φ P H U i.val := by
  have he := (signature_map φ P H U i).trans
    (Palette.projective φ P (catalogue H) U hn ρ hP i)
  exact (congrArg Sigma.fst he).symm
include hP in
theorem forwardRow (i : Fin (m+t)) (bits : List Bool) :
    Choice.table (table φ P H U) i.val bits =
      Palette.correction (catalogue H) hn i * Choice.table H (Palette.target ρ i).val bits := by
  rw [table_read]
  dsimp only [signature]
  rw [Palette.projective φ P (catalogue H) U hn ρ hP]
  simp [read,catalogue,Choice.table,(Palette.target ρ i).isLt]

def backwardArity (i : Fin t) : arity φ P H U (Palette.keyIndex (m:=m) i).val = a i.val := by
  have he := signature_map φ P H U (Palette.keyIndex (m:=m) i)
  dsimp only [signature] at he
  rw [Palette.signature_key,lifted_map] at he
  exact congrArg Sigma.fst he
theorem backwardRow (i : Fin t) (bits : List Bool) :
    Choice.table H i.val bits = Palette.pivot (catalogue H) hn i *
      Choice.table (table φ P H U) (Palette.keyIndex (m:=m) i).val bits := by
  rw [table_read]
  dsimp only [signature]
  rw [Palette.signature_key,lifted_map]
  have he := congrFun (recover_from_key (H i) (hn i)) (fun k => bits.getD k.val false)
  simpa [Choice.table,i.isLt,read,keyAny,Palette.pivot,catalogue] using he

def toOld : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (m+t) 1 (arity φ P H U))
      (GeneralOriginalTarget.originalPresentation (table φ P H U)).encoding
    (RawClosedNetwork.validatedEncoding t 1 a) (GeneralOriginalTarget.originalPresentation H).encoding
    (GeneralOriginalTarget.originalValue (table φ P H U)) (GeneralOriginalTarget.originalValue H) :=
  ScalarProgram.reduction (table φ P H U) H (Palette.target ρ) (forwardArity φ P H U hn ρ hP)
    (Palette.correction (catalogue H) hn) (forwardRow φ P H U hn ρ hP)

def fromOld : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 a) (GeneralOriginalTarget.originalPresentation H).encoding
    (RawClosedNetwork.validatedEncoding (m+t) 1 (arity φ P H U))
      (GeneralOriginalTarget.originalPresentation (table φ P H U)).encoding
    (GeneralOriginalTarget.originalValue H) (GeneralOriginalTarget.originalValue (table φ P H U)) :=
  ScalarProgram.reduction H (table φ P H U) (Palette.keyIndex (m:=m)) (backwardArity φ P H U)
    (Palette.pivot (catalogue H) hn) (backwardRow φ P H U hn)

end Holant.LocalDrafts.Hardness.FrozenFactorNormalization.PaletteCodec
