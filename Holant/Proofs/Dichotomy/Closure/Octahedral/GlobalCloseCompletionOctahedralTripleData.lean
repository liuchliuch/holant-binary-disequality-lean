import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPointData
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralModels
import Holant.Certificates.TetrahedralPreservers.RangeGeometry
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralLiteralDeck

/-! Coefficient extraction from the preserved marked-octahedral proof. Rank-three geometry uses the SAME four marked
24-point dictionaries. Every coordinate is computed in the existing exact
Q(sqrt2,i) field and embedded faithfully. No arbitrary endomorphism or tensor classification is supplied.
The current rank-three consumer uses separately checked fixed root hyperplanes
and separated projection witnesses.
-/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open scoped BigOperators Matrix

noncomputable def lift (v : RawVector) : V := fun i => embed (v i)

noncomputable def point (f : Form) (i : Fin 24) : V :=
  coordinates (complexMatrix (theta f (OctahedralSeparator.standard i)))

theorem lift_rawCoordinates (U : OctahedralSeparator.Mat) :
    lift (rawCoordinates U) = coordinates (complexMatrix U) := by
  ext i
  fin_cases i <;>
    simp [lift,rawCoordinates,coordinates_apply,
      Holant.Certificates.MatchingProductBridge.quaternionCoefficient,
      complexMatrix,embed_add,embed_sub,embed_neg,embed_mul,embed_div,
      embed_imag,show embed (2 : Scalar) = (2 : ℂ) from by
        change OctahedralSeparator.embedding (2 : Scalar) = (2 : ℂ)
        exact map_ofNat OctahedralSeparator.embedding 2]

theorem lift_point (f : Form) (i : Fin 24) : lift (rawPoint f i) = point f i := by
  rw [rawPoint_exact]
  exact lift_rawCoordinates _

@[simp] theorem lift_add (u v : RawVector) : lift (u+v) = lift u+lift v := by
  ext i
  exact embed_add _ _

@[simp] theorem lift_smul (c : Scalar) (v : RawVector) :
    lift (c • v) = embed c • lift v := by
  ext i
  exact embed_mul _ _

@[simp] theorem lift_zero : lift (0 : RawVector) = 0 := by
  ext i
  exact embed_zero

def rawPair (u v : RawVector) : Scalar :=
  u 0*v 0-u 1*v 1+u 2*v 2-u 3*v 3

def rawDot (u v : RawVector) : Scalar :=
  u 0*v 0+u 1*v 1+u 2*v 2+u 3*v 3

theorem embed_pair (u v : RawVector) :
    embed (rawPair u v) = pairing (lift u) (lift v) := by
  simp [rawPair,pairing,frobeniusSigns,lift,Fin.sum_univ_succ,
    embed_add,embed_sub,embed_mul]
  ring

def minor3 (u v w : RawVector) (a b c : Fin 4) : Scalar :=
  u a*(v b*w c-v c*w b)-u b*(v a*w c-v c*w a)+u c*(v a*w b-v b*w a)

/-- The four signed 3x3 minors of the actual three root vectors. -/
def rawNormal (u v w : RawVector) : RawVector :=
  ![minor3 u v w 1 2 3,-minor3 u v w 0 2 3,
    minor3 u v w 0 1 3,-minor3 u v w 0 1 2]

def normal (f : Form) (i j k : Fin 24) : RawVector :=
  rawNormal (rawPoint f i) (rawPoint f j) (rawPoint f k)

/-- A dependent triple has either a two-column proportionality relation or
the signed three-column relation witnessed by a nonzero 2x2 minor. -/
def relation (f : Form) (i j k : Fin 24) (mode : Bool) (a b : Fin 4) : Fin 3 → Scalar :=
  let u := rawPoint f i
  let v := rawPoint f j
  let w := rawPoint f k
  if mode then
    ![v a*w b-v b*w a,w a*u b-w b*u a,u a*v b-u b*v a]
  else ![v a,-u a,0]

def relationValid (f : Form) (i j k : Fin 24) (c : Fin 3 → Scalar) : Prop :=
  (∃ a : Fin 3, c a ≠ 0) ∧
    c 0 • rawPoint f i+c 1 • rawPoint f j+c 2 • rawPoint f k = 0

def dependent (f : Form) (i j k : Fin 24) : Prop :=
  ∃ mode : Bool, ∃ a b : Fin 4, relationValid f i j k (relation f i j k mode a b)

def planeIndices (f : Form) (i j k : Fin 24) : Finset (Fin 24) :=
  Finset.univ.filter fun r => rawDot (normal f i j k) (rawPoint f r) = 0

def projected (f : Form) (i j k r : Fin 24) : Fin 3 → Scalar :=
  ![rawPair (rawPoint f i) (rawPoint f r),
    rawPair (rawPoint f j) (rawPoint f r),
    rawPair (rawPoint f k) (rawPoint f r)]

def cross (u v : Fin 3 → Scalar) (a b : Fin 3) : Scalar := u a*v b-u b*v a

/-- The FIRST nonzero representative of each projected projective direction.
Killed root points are explicitly skipped. This is a finite filter on the
old 24 kernel indices; it does not select a map or tensor answer. -/
def projectedIndices (f : Form) (i j k : Fin 24) : Finset (Fin 24) :=
  Finset.univ.filter fun r =>
    projected f i j k r ≠ 0 ∧ ∀ s : Fin 24, s.val < r.val →
      projected f i j k s ≠ 0 →
      ∃ a b : Fin 3, cross (projected f i j k r) (projected f i j k s) a b ≠ 0

def finiteCertificate (f : Form) (i j k : Fin 24) : Prop :=
  dependent f i j k ∨
    (rawDot (normal f i j k) (rawPoint f i) = 0 ∧
     rawDot (normal f i j k) (rawPoint f j) = 0 ∧
     rawDot (normal f i j k) (rawPoint f k) = 0 ∧
     (planeIndices f i j k).card ≤ 9 ∧
     10 ≤ (projectedIndices f i j k).card)

instance (f : Form) (i j k : Fin 24) : Decidable (finiteCertificate f i j k) := by
  unfold finiteCertificate dependent relationValid
  infer_instance


/-- The same finite certificate, dispatched first by its four minor values
so independent triples do not search for a dependence witness. -/
def finiteCheck (f : Form) (i j k : Fin 24) : Prop :=
  if normal f i j k=0 then dependent f i j k else
    rawDot (normal f i j k) (rawPoint f i)=0 ∧
    rawDot (normal f i j k) (rawPoint f j)=0 ∧
    rawDot (normal f i j k) (rawPoint f k)=0 ∧
    (planeIndices f i j k).card≤9 ∧
    10≤(projectedIndices f i j k).card

instance (f : Form) (i j k : Fin 24) : Decidable (finiteCheck f i j k) := by
  unfold finiteCheck dependent relationValid
  infer_instance

theorem certificate_of_check (f : Form) (i j k : Fin 24)
    (h : finiteCheck f i j k) : finiteCertificate f i j k := by
  by_cases hz : normal f i j k=0
  · exact Or.inl (by simpa only [finiteCheck,if_pos hz] using h)
  · exact Or.inr (by simpa only [finiteCheck,if_neg hz] using h)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree

