import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionTensor
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineThreeFaces

/-! Genuine sparse low-rank descent by pinning selected original ports.
Every remaining physical port is retained, including dependent affine columns;
only actual pin values are substituted into the original row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankDescent
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open OrdinaryNegativeAffineSystematicSupport
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n r : ℕ}

/-- Increasing order is unnecessary: this is a genuine enumeration of a
finite set of original ports, with no identifications. -/
def port (S : Finset (Fin n)) (i : Fin S.card) : Fin n := (S.equivFin.symm i).val

@[simp] theorem port_mem (S : Finset (Fin n)) (i : Fin S.card) : port S i∈S :=
  (S.equivFin.symm i).property

theorem port_injective (S : Finset (Fin n)) : Function.Injective (port S) :=
  Subtype.val_injective.comp S.equivFin.symm.injective

/-- Extend free coordinates by literal fixed bits. -/
def fill (S : Finset (Fin n)) (z : Word n) (x : Word S.card) : Word n :=
  fun j=>if h : j∈S then x (S.equivFin ⟨j,h⟩) else z j

@[simp] theorem fill_port (S : Finset (Fin n)) (z : Word n) (x : Word S.card)
    (i : Fin S.card) : fill S z x (port S i)=x i := by simp [fill,port]

@[simp] theorem fill_outside (S : Finset (Fin n)) (z : Word n) (x : Word S.card)
    (j : Fin n) (hj : j∉S) : fill S z x j=z j := by simp [fill,hj]

theorem fill_affine (S : Finset (Fin n)) (z : Word n) : IsAffineMap (fill S z) := by
  intro x y
  funext j
  by_cases hj : j∈S
  · simp [fill,hj,AffinePhase.xor,origin]
  · cases hz : z j <;> simp [fill,hj,AffinePhase.xor,hz]

def system (S : Finset (Fin n)) (z : Word n) : AffineSystem n where
  rows := n
  matrix i j := if i∉S ∧ i=j then 1 else 0
  rhs i := if i∈S then 0 else bitValue (ZMod 2) (z i)

theorem system_holds (S : Finset (Fin n)) (z x : Word n) :
    (system S z).Holds x ↔ ∀i,i∉S → x i=z i := by
  classical
  constructor
  · intro h i hi
    have hh := h i
    simp only [system,hi,not_false_eq_true,true_and,ite_false] at hh
    simp at hh
    cases hx : x i <;> cases hz : z i <;> simp_all [bitValue]
  · intro h i
    by_cases hi : i∈S
    · simp [system,hi]
    · simp [system,hi,h i hi]

/-- Literal original gate minor. No support-coordinate/XOR gate is used. -/
def literal {K : Type*} (f : Signature K n) (S : Finset (Fin n)) (z : Word n) :
    Signature K S.card := fun x=>f (fill S z x)

def substitution (S : Finset (Fin n)) (z : Word n) : Fin n→Bool ⊕ Fin S.card :=
  fun j=>if h : j∈S then .inr (S.equivFin ⟨j,h⟩) else .inl (z j)

theorem literal_substitution {K : Type*} (f : Signature K n) (S : Finset (Fin n)) (z : Word n) :
    literal f S z=fun x=>f (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute
      (substitution S z) x) := by
  funext x
  unfold literal
  congr 1
  funext j
  by_cases hj : j∈S <;> simp [fill,substitution,
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute,hj]

/-- The set of still-exposed actual original ports. Only selected information
coordinates outside the face are pinned; all dependent columns remain. -/
def remaining {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
    (S : Finset (Fin r)) : Finset (Fin n) :=
  Finset.univ.filter (fun j=>∀i,i∉S → D.ports i≠j)

theorem remaining_iff {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
    (S : Finset (Fin r)) (j : Fin n) :
    j∈remaining D S ↔ ∀i,i∉S → D.ports i≠j := by simp [remaining]

theorem selected_remaining {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
    (S : Finset (Fin r)) (i : Fin r) : D.ports i∈remaining D S ↔ i∈S := by
  rw [remaining_iff]
  constructor
  · intro h
    by_contra hi
    exact h i hi rfl
  · intro hi j hj he
    exact hj (D.injective he ▸ hi)

/-- Projection of the original support after an actual original-port pinning. -/
def minor {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
    (S : Finset (Fin r)) (z : Word r) :
    Signature AlgebraicComplex (remaining D S).card :=
  literal f (remaining D S) (D.encode z)


def project (S : Finset (Fin n)) (x : Word n) : Word S.card := fun j=>x (port S j)

theorem fill_project (S : Finset (Fin n)) (z x : Word n)
    (h : ∀i,i∉S → x i=z i) : fill S z (project S x)=x := by
  funext i
  by_cases hi : i∈S
  · simp [fill,project,port,hi]
  · simp [fill,hi,h i hi]

@[simp] theorem project_fill (S : Finset (Fin n)) (z : Word n) (x : Word S.card) :
    project S (fill S z x)=x := by funext i;exact fill_port S z x i

theorem project_affine (S : Finset (Fin n)) : IsAffineMap (project S) :=
  coordinates_isAffineMap (port S)

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)

/-- Reinstalling the selected pins leaves each supported chart point intact. -/
theorem fill_remaining (S : Finset (Fin r)) (z x : Word r)
    (h : ∀i,i∉S → x i=z i) :
    fill (remaining D S) (D.encode z) (project (remaining D S) (D.encode x))=D.encode x := by
  apply fill_project
  intro j hj
  have hj' : ¬∀i,i∉S → D.ports i≠j := by simpa [remaining_iff] using hj
  push Not at hj'
  obtain ⟨i,hi,rfl⟩ := hj'
  rw [D.free,D.free,h i hi]

def minorPorts (S : Finset (Fin r)) : Fin S.card→Fin (remaining D S).card :=
  fun i=>(remaining D S).equivFin ⟨D.ports (port S i),
    (selected_remaining D S _).mpr (port_mem S i)⟩

theorem minorPorts_injective (S : Finset (Fin r)) : Function.Injective (minorPorts D S) := by
  intro i j he
  have hv := congrArg (fun k=>port (remaining D S) k) he
  have h : D.ports (port S i)=D.ports (port S j) := by simpa [minorPorts,port] using hv
  exact port_injective S (D.injective h)

def minorEncode (S : Finset (Fin r)) (z : Word r) (x : Word S.card) :
    Word (remaining D S).card := project (remaining D S) (D.encode (fill S z x))

theorem minor_value (S : Finset (Fin r)) (z : Word r) (x : Word S.card) :
    minor D S z (minorEncode D S z x)=f (D.encode (fill S z x)) := by
  unfold minor literal minorEncode
  rw [fill_remaining D S z _ (fun i hi=>fill_outside S z x i hi)]

/-- Exact low-rank chart of the actual original-port minor. -/
def minorChart (S : Finset (Fin r)) (z : Word r) :
    SystematicSupport (minor D S z) S.card where
  ports := minorPorts D S
  injective := minorPorts_injective D S
  encode := minorEncode D S z
  affine := by
    change IsAffineMap (fun x=>project (remaining D S) (D.encode (fill S z x)))
    exact affine_map_comp (project (remaining D S)) (fun x=>D.encode (fill S z x))
      (project_affine _) (affine_map_comp D.encode (fill S z) D.affine (fill_affine S z))
  free x i := by simp [minorEncode,project,minorPorts,port,D.free,fill]
  supported x := by rw [minor_value];exact D.supported _
  covers x hx := by
    let q := fill (remaining D S) (D.encode z) x
    have hq : f q≠0 := hx
    let v : Word r := fun i=>q (D.ports i)
    have hv : ∀i,i∉S → v i=z i := by
      intro i hi
      have hn : D.ports i∉remaining D S := mt (selected_remaining D S i).mp hi
      simpa [v,q,fill_outside _ _ _ _ hn] using D.free z i
    have hd : (fun j=>x (minorPorts D S j))=project S v := by
      funext j
      simp [project,v,q,fill,minorPorts,(selected_remaining D S _).mpr (port_mem S j)]
    change project (remaining D S) (D.encode (fill S z (fun j=>x (minorPorts D S j))))=x
    rw [hd,fill_project S z v hv,D.covers q hq]
    exact project_fill _ _ x

/-- The compressed row is used only as a semantic value identity. -/
theorem minorChart_reduced (S : Finset (Fin r)) (z : Word r) :
    (minorChart D S z).reduced=literal D.reduced S z := by
  funext x
  exact minor_value D S z x

/-- Every retained logical face is nonzero by the exact support chart. -/
theorem minor_nonzero (S : Finset (Fin r)) (z : Word r) : minor D S z≠0 := by
  intro hz
  exact (minorChart D S z).supported (origin _) (congrFun hz _)

/-- Actual original-coordinate pinning preserves the Affine square. -/
theorem minor_square (S : Finset (Fin r)) (z : Word r)
    (h : Affine (fun x=>f x^2)) : Affine (fun x=>minor D S z x^2) :=
  h.precompose _ (fill_affine _ _)

/-- Affinity of the physical minor would imply affinity of the entire
pinned logical face, including its explicit support equations. -/
theorem face_affine_of_minor (S : Finset (Fin r)) (z : Word r)
    (h : Affine (minor D S z)) :
    Affine (OrdinaryNegativeAffineThreeFaces.face D.reduced S z) := by
  have hmap : IsAffineMap (fun x=>project (remaining D S) (D.encode x)) :=
    affine_map_comp _ _ (project_affine _) D.affine
  have ha := (h.precompose _ hmap).restrict (system S z)
  convert ha using 1
  funext x
  by_cases hx : ∀i,i∉S → x i=z i
  · rw [ite_eq_left ((system_holds S z x).mpr hx)]
    change (if ∀i,i∉S → x i=z i then f (D.encode x) else 0)=
      f (fill (remaining D S) (D.encode z) (project (remaining D S) (D.encode x)))
    rw [ite_eq_left hx,fill_remaining D S z x hx]
  · simp only [OrdinaryNegativeAffineThreeFaces.face,ite_eq_right hx,
      ite_eq_right (mt (system_holds S z x).mp hx)]

/-- A nonaffine affine-square row has a genuine literal pinning minor with
at most three information coordinates. The physical arity is not compressed. -/
theorem exists_low_rank_minor (square : Affine (fun x=>f x^2)) (nonzero : f≠0)
    (bad : ¬Affine f) :
    ∃r : ℕ,∃D : SystematicSupport f r,∃S : Finset (Fin r),∃z : Word r,
      S.card≤3 ∧ ¬Affine (minor D S z) ∧
      Affine (fun x=>minor D S z x^2) ∧
      Fintype.card {x : Word (remaining D S).card // minor D S z x≠0}=2^S.card := by
  obtain ⟨r,⟨D⟩⟩ := exists_of_affine_square f square nonzero
  obtain ⟨S,hS,z,hz⟩ := OrdinaryNegativeAffineThreeFaces.exists_bad_face
    D.reduced D.reduced_full (D.nonAffine_reduced square nonzero bad)
  refine ⟨r,D,S,z,hS,fun h=>hz (face_affine_of_minor D S z h),?_,(minorChart D S z).support_card⟩
  exact square.precompose _ (fill_affine _ _)

include D in
/-- Rank zero is a genuine singleton support, hence cannot be the retained
nonaffine witness. -/
theorem rank_positive (square : Affine (fun x=>f x^2)) (nonzero : f≠0)
    (bad : ¬Affine f) : 0<r := by
  by_contra hr
  have hr0 : r=0 := by omega
  subst r
  apply D.nonAffine_reduced square nonzero bad
  convert affine_constant 0 (D.reduced (origin 0)) using 1
  funext x
  congr 1
  funext i
  exact Fin.elim0 i

/-- The physical descent has one, two, or three independent coordinates,
with all original dependent coordinates retained. -/
theorem exists_positive_low_rank_minor (square : Affine (fun x=>f x^2)) (nonzero : f≠0)
    (bad : ¬Affine f) :
    ∃r : ℕ,∃D : SystematicSupport f r,∃S : Finset (Fin r),∃z : Word r,
      1≤S.card ∧ S.card≤3 ∧ ¬Affine (minor D S z) ∧
      Affine (fun x=>minor D S z x^2) ∧
      Fintype.card {x : Word (remaining D S).card // minor D S z x≠0}=2^S.card := by
  obtain ⟨r,D,S,z,upper,bad,square,count⟩ := exists_low_rank_minor square nonzero bad
  have hn : minor D S z≠0 := by
    intro hz
    exact (minorChart D S z).supported (origin _) (congrFun hz _)
  exact ⟨r,D,S,z,rank_positive (minorChart D S z) square hn bad,upper,bad,square,count⟩

/-- Every exposed coordinate comes from exactly one original port. Thus the
substitution is pure pinning rather than an identification minor. -/
theorem substitution_unique (S : Finset (Fin n)) (z : Word n) (i : Fin S.card) :
    ∃!j : Fin n,substitution S z j=Sum.inr i := by
  refine ⟨port S i,by simp [substitution,port],?_⟩
  intro j hj
  by_cases h : j∈S
  · have he : S.equivFin ⟨j,h⟩=i := by simpa [substitution,h] using hj
    have hv := congrArg (fun t=>port S t) he
    simpa [port] using hv
  · simp [substitution,h] at hj

/-- The complete original-field interface: an actual pin substitution,
unchanged source coefficients, a selected physical information set of rank
one through three, and a nonaffine affine-square restricted row. -/
theorem exists_original_low_rank {K : IntermediateField ℚ AlgebraicComplex}
    (f : Signature K n) (square : Affine (fun x=>(f x : AlgebraicComplex)^2))
    (nonzero : f≠0) (bad : ¬Affine (fun x=>(f x : AlgebraicComplex))) :
    ∃m k : ℕ,∃p : Fin n→Bool ⊕ Fin m,
      1≤k ∧ k≤3 ∧ (∀i : Fin m,∃!j : Fin n,p j=Sum.inr i) ∧
      Nonempty (SystematicSupport
        (fun x=>(f (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute p x) : AlgebraicComplex)) k) ∧
      ¬Affine (fun x=>(f (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute p x) : AlgebraicComplex)) ∧
      Affine (fun x=>(f (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute p x) : AlgebraicComplex)^2) := by
  let F : Signature AlgebraicComplex n := fun x=>(f x : AlgebraicComplex)
  have hn : F≠0 := by
    intro hz
    apply nonzero
    funext x
    exact Subtype.ext (congrFun hz x)
  obtain ⟨r,D,S,z,lo,hi,hbad,hsquare,hcard⟩ := exists_positive_low_rank_minor square hn bad
  let p := substitution (remaining D S) (D.encode z)
  have he : (fun x=>(f (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute p x) : AlgebraicComplex))=
      minor D S z := (literal_substitution F (remaining D S) (D.encode z)).symm
  refine ⟨(remaining D S).card,S.card,p,lo,hi,substitution_unique _ _,?_,?_,?_⟩
  · rw [he];exact ⟨minorChart D S z⟩
  · rwa [he]
  · change Affine (fun x=>(fun y=>(f (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute p y) : AlgebraicComplex)) x^2)
    rw [he]
    exact hsquare


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankDescent
end
