import Holant.Algebraic.FixedFamilySize
import Holant.NetworkAlgebra

/-!
# Executable coefficient semiring for fixed-field graph evaluation

The runtime objects contain only rational vectors and the fixed rational table.
A semantic fixed-field basis is used solely to prove table laws, never to perform
an addition or multiplication. This lets generic graph/program constructions run
on coordinate data before their separate finite-machine compilation.
-/

namespace Holant.Algebraic

namespace ArithmeticData

/-- Algebraic laws for the finite table. These are propositions, erased at runtime. -/
structure Laws {n : ℕ} (D : ArithmeticData n) : Prop where
  mul_assoc : ∀ u v w, D.mulCode (D.mulCode u v) w = D.mulCode u (D.mulCode v w)
  mul_comm : ∀ u v, D.mulCode u v = D.mulCode v u
  one_mul : ∀ v, D.mulCode D.unitCode v = v
  mul_one : ∀ v, D.mulCode v D.unitCode = v
  zero_mul : ∀ v, D.mulCode 0 v = 0
  mul_zero : ∀ v, D.mulCode v 0 = 0
  left_distrib : ∀ u v w, D.mulCode u (v + w) = D.mulCode u v + D.mulCode u w
  right_distrib : ∀ u v w, D.mulCode (u + v) w = D.mulCode u w + D.mulCode v w

end ArithmeticData

/-- The actual field interpretation proves every table law by injectivity. -/
theorem FixedField.table_laws {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : FixedField K n) : F.toArithmeticData.Laws := by
  have hm (v w : Fin n → ℚ) : F.decode (F.toArithmeticData.mulCode v w) =
      F.decode v * F.decode w := F.decode_mul v w
  constructor
  all_goals intros
  all_goals apply F.decode_injective
  all_goals simp [hm, map_add, map_zero, F.decode_unit, _root_.mul_assoc, _root_.mul_comm, _root_.mul_left_comm, mul_add, add_mul]

/-- A tagged rational vector, so table multiplication cannot be confused with
coordinatewise multiplication on an ordinary function type. -/
structure Coordinates {n : ℕ} (D : ArithmeticData n) where
  coeff : Fin n → ℚ

namespace Coordinates

variable {n : ℕ} {D : ArithmeticData n}

@[ext] theorem ext {a b : Coordinates D} (h : a.coeff = b.coeff) : a = b := by
  cases a; cases b; cases h; rfl

instance : Zero (Coordinates D) := ⟨⟨0⟩⟩
instance : One (Coordinates D) := ⟨⟨D.unitCode⟩⟩
instance : Add (Coordinates D) := ⟨fun a b => ⟨a.coeff + b.coeff⟩⟩
instance : Mul (Coordinates D) := ⟨fun a b => ⟨D.mulCode a.coeff b.coeff⟩⟩
instance : SMul ℕ (Coordinates D) := ⟨fun k a => ⟨k • a.coeff⟩⟩
instance : NatCast (Coordinates D) := ⟨fun k => ⟨k • D.unitCode⟩⟩

def pow (a : Coordinates D) : ℕ → Coordinates D
  | 0 => 1
  | k + 1 => pow a k * a

instance : Pow (Coordinates D) ℕ := ⟨pow⟩

@[simp] theorem coeff_zero : (0 : Coordinates D).coeff = 0 := rfl
@[simp] theorem coeff_one : (1 : Coordinates D).coeff = D.unitCode := rfl
@[simp] theorem coeff_add (a b : Coordinates D) : (a + b).coeff = a.coeff + b.coeff := rfl
@[simp] theorem coeff_mul (a b : Coordinates D) : (a * b).coeff = D.mulCode a.coeff b.coeff := rfl
@[simp] theorem coeff_nsmul (k : ℕ) (a : Coordinates D) : (k • a).coeff = k • a.coeff := rfl
@[simp] theorem coeff_natCast (k : ℕ) : (k : Coordinates D).coeff = k • D.unitCode := rfl

/-- All computational fields use only finite rational data. The basis appears
only in a possible proof of `h`, which is erased from compiled evaluation. -/
abbrev commSemiring (h : D.Laws) : CommSemiring (Coordinates D) where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc a b c := ext (add_assoc _ _ _)
  zero_add a := ext (zero_add _)
  add_zero a := ext (add_zero _)
  add_comm a b := ext (add_comm _ _)
  mul_assoc a b c := ext (h.mul_assoc _ _ _)
  one_mul a := ext (h.one_mul _)
  mul_one a := ext (h.mul_one _)
  mul_comm a b := ext (h.mul_comm _ _)
  zero_mul a := ext (h.zero_mul _)
  mul_zero a := ext (h.mul_zero _)
  left_distrib a b c := ext (h.left_distrib _ _ _)
  right_distrib a b c := ext (h.right_distrib _ _ _)
  nsmul := (· • ·)
  nsmul_zero a := ext (zero_nsmul _)
  nsmul_succ k a := ext (succ_nsmul _ _)
  npow := fun k a => pow a k
  npow_zero a := rfl
  npow_succ k a := rfl
  natCast := fun k => ⟨k • D.unitCode⟩
  natCast_zero := ext (zero_nsmul _)
  natCast_succ k := ext (succ_nsmul _ _)

/-- The representation uses the already established exact vector encoding. -/
def encoding (D : ArithmeticData n) : Computability.Encoding (Coordinates D) Bool where
  encode a := (vectorEncoding n).encode a.coeff
  decode bits := ((vectorEncoding n).decode bits).map (fun v => ⟨v⟩)
  decode_encode a := by simp

end Coordinates
namespace FixedField

variable {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ} (F : FixedField K n)

local instance coordinateSemiring : CommSemiring (Coordinates F.toArithmeticData) :=
  Coordinates.commSemiring F.table_laws

/-- Semantic interpretation of the executable coefficient object. The basis is
present only in this correctness map, not in the coordinate operations. -/
noncomputable def coordinateMap : Coordinates F.toArithmeticData →+* K where
  toFun v := F.decode v.coeff
  map_zero' := map_zero F.decode
  map_one' := F.decode_unit
  map_add' v w := F.decode_add v.coeff w.coeff
  map_mul' v w := F.decode_mul v.coeff w.coeff

@[simp] theorem coordinateMap_apply (v : Coordinates F.toArithmeticData) :
    F.coordinateMap v = F.decode v.coeff := rfl

/-- Canonical coordinate bytes are exactly the established semantic field bytes. -/
@[simp] theorem encoding_coordinateMap (v : Coordinates F.toArithmeticData) :
    F.encoding.encode (F.coordinateMap v) = (Coordinates.encoding F.toArithmeticData).encode v :=
  F.encoding_decode v.coeff

theorem coordinateMap_injective : Function.Injective F.coordinateMap := by
  intro v w h
  apply Coordinates.ext
  exact F.decode_injective h

/-- Independent full assignment sums over coefficient data agree exactly with
semantic field network values, including loops, nullary and empty networks. -/
theorem coordinateNetwork_denote {ports : ℕ}
    (N : Holant.Network (Coordinates F.toArithmeticData) ports) (x : Fin ports → Bool) :
    (N.map F.coordinateMap).denote x = F.coordinateMap (N.denote x) :=
  N.denote_map F.coordinateMap x

end FixedField

end Holant.Algebraic
