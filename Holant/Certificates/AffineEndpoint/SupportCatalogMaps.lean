import Holant.Certificates.AffineEndpoint.SupportCatalogData

/-! Actual affine word maps and finite equation systems for the literal rows. -/
namespace Holant.Certificates.AffineEndpoint.SupportCatalog
open Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
set_option backward.isDefEq.respectTransparency false

def linearDim (l : LinearIndex) : ℕ := (linearRows l).dimension.val
def linearWords (l : LinearIndex) : Finset (Word 4) := decodeSupport (linearRows l).codes

def generatorMatrix (l : LinearIndex) : Fin 4 → Fin (linearDim l) → ZMod 2 :=
  fun p j => bitValue (ZMod 2) (codeWord ((linearRows l).generators j) p)

def coordinateMatrix (l : LinearIndex) : Fin (linearDim l) → Fin 4 → ZMod 2 :=
  fun j p => bitValue (ZMod 2) (codeWord ((linearRows l).dual j) p)

def equationMatrix (l : LinearIndex) : Fin 4 → Fin 4 → ZMod 2 :=
  fun r p => bitValue (ZMod 2) (codeWord ((linearRows l).equations r) p)

def linearChart (l : LinearIndex) : Word (linearDim l) → Word 4 := matrixWord (generatorMatrix l)
def linearCoordinates (l : LinearIndex) : Word 4 → Word (linearDim l) := matrixWord (coordinateMatrix l)

def linearSystem (l : LinearIndex) : AffineSystem 4 :=
  ⟨4, equationMatrix l, fun _ => 0⟩

def supportLinearIndex (s : SupportIndex) : LinearIndex := (supportRows s).linearIndex
def supportDim (s : SupportIndex) : ℕ := linearDim (supportLinearIndex s)
def supportOrigin (s : SupportIndex) : Word 4 := codeWord (supportRows s).originCode
def supportWords (s : SupportIndex) : Finset (Word 4) := decodeSupport (supportRows s).codes

def supportChart (s : SupportIndex) (y : Word (supportDim s)) : Word 4 :=
  xor (supportOrigin s) (linearChart (supportLinearIndex s) y)

def supportCoordinates (s : SupportIndex) (x : Word 4) : Word (supportDim s) :=
  linearCoordinates (supportLinearIndex s) (xor (supportOrigin s) x)

def supportSystem (s : SupportIndex) : AffineSystem 4 where
  rows := 4
  matrix := equationMatrix (supportLinearIndex s)
  rhs r := rowDot (equationMatrix (supportLinearIndex s) r) (supportOrigin s)

theorem supportDim_le_four (s : SupportIndex) : supportDim s ≤ 4 :=
  Nat.le_of_lt_succ (linearRows (supportLinearIndex s)).dimension.isLt

theorem supportChart_affine (s : SupportIndex) : IsAffineMap (supportChart s) :=
  translated_matrixWord_affine _ _

theorem supportCoordinates_affine (s : SupportIndex) : IsAffineMap (supportCoordinates s) :=
  matrixWord_translate_affine _ _

theorem chart_origin (s : SupportIndex) : supportChart s (origin (supportDim s)) = supportOrigin s := by
  simp [supportChart, linearChart, supportDim]

theorem supportSystem_shift_holds (s : SupportIndex) (x : Word 4) :
    (supportSystem s).Holds x ↔
      (linearSystem (supportLinearIndex s)).Holds (xor (supportOrigin s) x) := by
  change (∀ r, rowDot (equationMatrix (supportLinearIndex s) r) x =
      rowDot (equationMatrix (supportLinearIndex s) r) (supportOrigin s)) ↔
    (∀ r, rowDot (equationMatrix (supportLinearIndex s) r) (xor (supportOrigin s) x) = 0)
  apply forall_congr'
  intro r
  rw [rowDot_xor]
  have h : ∀ a b : ZMod 2, a = b ↔ b + a = 0 := by decide
  exact h _ _

end Holant.Certificates.AffineEndpoint.SupportCatalog
