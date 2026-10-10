import Holant.Proofs.Tractability.EOEvaluation.PairLift
import Holant.Proofs.Reductions.EightVertexNonexception.SparseExclusions

/-! A central missing triple-xor witness produces an actual oriented perfect
pairing whose restriction fails BOTH source classes. The pairing is constructed
from the four-word central affine plane by the proved character-multiplicity
matching; no pairing witness, class failure, or hardness result is supplied.
This isolates a fixed-table structural step and does not declare the pairing
restriction to be a freely available physical signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativePairing
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace PC
export Holant.LocalDrafts.Tractability.EOEvaluation.PairingConstruction (pairing covers twice_count)
end PC
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift
  (Compatible compress word_compress restrict affine_lift product_lift)
end L
namespace D
export Holant.LocalDrafts.Tractability.EOEvaluation.PairingCharacters (Data)
end D
set_option backward.isDefEq.respectTransparency false

private def bitPlane (a b c : Bool) (u : Bool×Bool) : Bool :=
  Bool.xor (Bool.xor a (u.1 && Bool.xor a b)) (u.2 && Bool.xor a c)
private def indexTriple (u v w : Bool×Bool) : Bool×Bool :=
  (Bool.xor (Bool.xor u.1 v.1) w.1,Bool.xor (Bool.xor u.2 v.2) w.2)
private theorem bitPlane_triple : ∀a b c u v w,
    Bool.xor (Bool.xor (bitPlane a b c u) (bitPlane a b c v)) (bitPlane a b c w)=
      bitPlane a b c (indexTriple u v w) := by
  intro a b c u v w
  rcases u with ⟨u₀,u₁⟩
  rcases v with ⟨v₀,v₁⟩
  rcases w with ⟨w₀,w₁⟩
  cases a <;> cases b <;> cases c <;> cases u₀ <;> cases u₁ <;>
    cases v₀ <;> cases v₁ <;> cases w₀ <;> cases w₁ <;> rfl

variable {n : ℕ} (a b c : Fin n→Bool)

def plane (u : Bool×Bool) : Fin n→Bool := fun j=>bitPlane (a j) (b j) (c j) u

@[simp] theorem plane_zero : plane a b c (false,false)=a := by
  funext j
  dsimp [plane,bitPlane,tripleXor]
  cases a j <;> rfl
@[simp] theorem plane_first : plane a b c (true,false)=b := by
  funext j
  dsimp [plane,bitPlane,tripleXor]
  cases a j <;> cases b j <;> rfl
@[simp] theorem plane_second : plane a b c (false,true)=c := by
  funext j
  dsimp [plane,bitPlane,tripleXor]
  cases a j <;> cases c j <;> rfl
@[simp] theorem plane_third : plane a b c (true,true)=tripleXor a b c := by
  funext j
  dsimp [plane,bitPlane,tripleXor]
  cases a j <;> cases b j <;> cases c j <;> rfl

theorem plane_triple (u v w : Bool×Bool) :
    tripleXor (plane a b c u) (plane a b c v) (plane a b c w)=
      plane a b c (indexTriple u v w) := by
  funext j
  exact bitPlane_triple (a j) (b j) (c j) u v w

def points : Finset (Fin n→Bool) := Finset.univ.image (plane a b c)

theorem mem_points (u : Bool×Bool) : plane a b c u∈points a b c :=
  Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩

def planeData (ha : charge a=0) (hb : charge b=0) (hc : charge c=0)
    (hd : charge (tripleXor a b c)=0) : D.Data n where
  points := points a b c
  base := ⟨a,by simpa using mem_points a b c (false,false)⟩
  closed := by
    intro x hx y hy z hz
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hz
    rw [plane_triple]
    exact mem_points a b c _
  central := by
    intro x hx
    obtain ⟨⟨u,v⟩,_,rfl⟩ := Finset.mem_image.mp hx
    cases u <;> cases v
    · simpa using ha
    · simpa using hc
    · simpa using hb
    · simpa using hd

variable {a b c}
variable (f : Signature AlgebraicComplex n) (he : Signature.CentralSupport f)
variable (ha : f a≠0) (hb : f b≠0) (hc : f c≠0)
variable (hz : f (tripleXor a b c)=0) (hd : charge (tripleXor a b c)=0)

include he in
private theorem supported_charge (x : Fin n→Bool) (hx : f x≠0) : charge x=0 := by
  have hw : 2*weight x=n := by
    by_contra hn
    exact hx (he x hn)
  unfold charge
  omega

def data : D.Data n := planeData a b c
  (supported_charge f he a ha) (supported_charge f he b hb)
  (supported_charge f he c hc) hd

def pairing : OrientedPerfectPairing n := PC.pairing (data f he ha hb hc hd)

theorem compatible (u : Bool×Bool) : L.Compatible (pairing f he ha hb hc hd) (plane a b c u) :=
  PC.covers (data f he ha hb hc hd) _ (mem_points a b c u)

theorem pairing_count : 2*(pairing f he ha hb hc hd).count=n :=
  PC.twice_count (data f he ha hb hc hd)

/-- The constructed pairing keeps the three original nonzero values exactly. -/
theorem compressed_values :
    (pairing f he ha hb hc hd).restrict f (L.compress (pairing f he ha hb hc hd) a)=f a ∧
    (pairing f he ha hb hc hd).restrict f (L.compress (pairing f he ha hb hc hd) b)=f b ∧
    (pairing f he ha hb hc hd).restrict f (L.compress (pairing f he ha hb hc hd) c)=f c := by
  have h0 : L.Compatible (pairing f he ha hb hc hd) a := by
    simpa using compatible f he ha hb hc hd (false,false)
  have h1 : L.Compatible (pairing f he ha hb hc hd) b := by
    simpa using compatible f he ha hb hc hd (true,false)
  have h2 : L.Compatible (pairing f he ha hb hc hd) c := by
    simpa using compatible f he ha hb hc hd (false,true)
  simp only [OrientedPerfectPairing.restrict,L.word_compress _ _ h0,
    L.word_compress _ _ h1,L.word_compress _ _ h2,and_self]

include hz in
/-- A balanced support hole obstructs both affine and product pairing classes,
with the same explicitly constructed pairing. -/
theorem pairing_bad :
    ¬Affine ((pairing f he ha hb hc hd).restrict f) ∧
    ¬Product ((pairing f he ha hb hc hd).restrict f) := by
  let p := pairing f he ha hb hc hd
  have h0 : L.Compatible p a := by simpa [p] using compatible f he ha hb hc hd (false,false)
  have h1 : L.Compatible p b := by simpa [p] using compatible f he ha hb hc hd (true,false)
  have h2 : L.Compatible p c := by simpa [p] using compatible f he ha hb hc hd (false,true)
  have hn0 : L.restrict p f a≠0 := by simpa [L.restrict,h0] using ha
  have hn1 : L.restrict p f b≠0 := by simpa [L.restrict,h1] using hb
  have hn2 : L.restrict p f c≠0 := by simpa [L.restrict,h2] using hc
  have hn3 : L.restrict p f (xor3 a b c)=0 := by
    change (if L.Compatible p (tripleXor a b c) then f (tripleXor a b c) else 0)=0
    simp [hz]
  constructor
  · intro hh
    exact affine_support_xor3 (L.affine_lift p hh) a b c hn0 hn1 hn2 hn3
  · intro hh
    exact product_support_xor3 (L.product_lift p hh) a b c hn0 hn1 hn2 hn3

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativePairing
