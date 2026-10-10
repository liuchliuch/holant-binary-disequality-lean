import Holant.Certificates.OctahedralSeparator.Field
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/-! Literal marked-form matrices and exact finite source parameters for A.16.
Forms0/1/2/3 are O/O-prime/O_dt/O_td, in the original fixed-I coordinates. -/
namespace Holant.Certificates.OctahedralSeparator

abbrev Form := Fin 4
abbrev Mat := Bool → Bool → Scalar
abbrev Word := Fin 4 → Bool

def mat (a b c d : Scalar) : Mat := fun x y => if x then if y then d else c else if y then b else a

def q : Fin 4 → Mat :=
  ![mat 1 0 0 1,mat 0 imag imag 0,mat 0 1 (-1) 0,mat imag 0 0 (-imag)]
def flip : Mat := mat 0 1 1 0

def mm (U V : Mat) : Mat := fun a b => U a false*V false b+U a true*V true b
def mt (U : Mat) : Mat := fun a b => U b a
def ms (c : Scalar) (U : Mat) : Mat := fun a b => c*U a b
def determinant (U : Mat) : Scalar := U false false*U true true-U false true*U true false

def signs : Fin 8 → Fin 3 → Bool :=
  ![![false,false,false],![false,false,true],![false,true,false],![false,true,true],
    ![true,false,false],![true,false,true],![true,true,false],![true,true,true]]
def signed (ε : Fin 3 → Bool) : Mat := q 0+
  ms (if ε 0 then -1 else 1) (q 1)+ms (if ε 1 then -1 else 1) (q 2)+ms (if ε 2 then -1 else 1) (q 3)

def standard : Fin 24 → Mat :=
  ![q 0,q 1,q 2,q 3,signed (signs 0),signed (signs 1),signed (signs 2),signed (signs 3),
    signed (signs 4),signed (signs 5),signed (signs 6),signed (signs 7),
    q 0+q 1,q 0-q 1,q 0+q 2,q 0-q 2,q 0+q 3,q 0-q 3,
    q 1+q 2,q 1-q 2,q 1+q 3,q 1-q 3,q 2+q 3,q 2-q 3]

def conjugator : Form → Mat :=
  ![q 0,mat root (-(imag*root)) (1-imag) (1+imag),
    q 0-ms (root-1) (q 1),q 0+ms (root-1) (q 3)]

/-- Explicit exact inverses; the two-sided identities below check every entry. -/
def inverseConjugator : Form → Mat :=
  ![q 0,
    mat (coeff 0 (1/4) 0 0) (coeff (1/4) 0 (1/4) 0)
      (coeff 0 0 0 (1/4)) (coeff (1/4) 0 (-1/4) 0),
    mat (coeff (1/2) (1/4) 0 0) (coeff 0 0 0 (1/4))
      (coeff 0 0 0 (1/4)) (coeff (1/2) (1/4) 0 0),
    mat (coeff (1/2) (1/4) 0 (-1/4)) 0 0 (coeff (1/2) (1/4) 0 (1/4))]

def theta (f : Form) (U : Mat) : Mat := mm (inverseConjugator f) (mm U (conjugator f))
def pull (f : Form) (U : Mat) : Mat := mm (conjugator f) (mm U (inverseConjugator f))
def sMatrix (f : Form) : Mat := mm (conjugator f) (mt (conjugator f))
def sInverse (f : Form) : Mat := mm (mt (inverseConjugator f)) (inverseConjugator f)
def correction (f : Form) : Mat := theta f (sInverse f)
def coefficientLegs (f : Form) : Fin 4 → Mat :=
  ![inverseConjugator f,mt (conjugator f),inverseConjugator f,mt (conjugator f)]

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem conjugator_inverses : ∀ f : Form,
    mm (conjugator f) (inverseConjugator f)=q 0 ∧ mm (inverseConjugator f) (conjugator f)=q 0 := by decide +kernel

theorem conjugator_det_nonzero : ∀ f : Form, determinant (conjugator f) ≠ 0 := by decide +kernel

theorem standard_det_nonzero : ∀ k : Fin 24, determinant (standard k) ≠ 0 := by decide +kernel

/-- The actual port2/4 correction converts H^T into H^-1 exactly. -/
theorem correction_cancels : ∀ f : Form,
    mm (correction f) (mt (conjugator f))=inverseConjugator f := by decide +kernel

end Holant.Certificates.OctahedralSeparator
