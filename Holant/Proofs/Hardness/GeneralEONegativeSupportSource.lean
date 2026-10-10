import Holant.Proofs.Hardness.GeneralEONegativeSupportTensor
import Holant.Proofs.Hardness.GeneralEONegativeTensorAccess
import Holant.Proofs.Hardness.GeneralEONegativePairing
import Holant.Proofs.Hardness.EONegativePairReduction

/-! Unconditional arbitrary-arity support-obstruction producer. Two original
failed shared-sign choices produce one central-hole EO macro and its physical
original-field source reduction. Charge-zero witnesses use one original copy;
strictly opposite witnesses use the internally calculated tensor multiplicities.
The resulting paired restriction is proved outside both A and P. No assertion
that this restriction is physically available, or that the original problem is
already hard, is smuggled into the interface. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeSupportSource
open Holant Holant.Tractable Holant.Complexity
open GeneralEONegativeSupportTensor
namespace C
export GeneralEONegativeTensorCore (graph word triple_word supported_word missing_word charge_word central)
end C
namespace W
export EONegativeWitness (Supports support_failure pairing_failure)
end W
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

/-- Every row of this fixed macro is an actual original dictionary label. -/
structure Source where
  copies : ℕ
  labels : Fin copies→Fin s
  central : Signature.CentralSupport (C.graph labels G).denote
  hole : CentralHole (C.graph labels G).denote

abbrev Source.graph (D : Source G) := C.graph D.labels G

def literal (i : Fin s) (T : Triple (G i)) (he : Signature.CentralSupport (G i))
    (hz : G i T.xor=0) (hq : charge T.xor=0) : Source G := by
  let ls : Fin 1→Fin s := fun _=>i
  let Q : Triple (C.graph ls G).denote := {
    first := C.word ls (fun _=>T.first)
    second := C.word ls (fun _=>T.second)
    third := C.word ls (fun _=>T.third)
    first_supported := C.supported_word ls G _ (fun _=>T.first_supported)
    second_supported := C.supported_word ls G _ (fun _=>T.second_supported)
    third_supported := C.supported_word ls G _ (fun _=>T.third_supported) }
  refine ⟨1,ls,C.central ls G (fun _=>he),Q,?_,?_⟩
  · change (C.graph ls G).denote
      (tripleXor (C.word ls (fun _=>T.first)) (C.word ls (fun _=>T.second))
        (C.word ls (fun _=>T.third)))=0
    rw [C.triple_word]
    exact C.missing_word ls G _ 0 hz
  · change charge (tripleXor (C.word ls (fun _=>T.first)) (C.word ls (fun _=>T.second))
        (C.word ls (fun _=>T.third)))=0
    rw [C.triple_word,C.charge_word]
    simpa [Triple.xor] using hq

/-- Both weak-side failures are accepted, including either charge-zero case. -/
theorem exists_source (i j : Fin s) (hei : Signature.CentralSupport (G i))
    (hej : Signature.CentralSupport (G j))
    (hp : ¬W.Supports .positive ⟨a i.val,G i⟩)
    (hn : ¬W.Supports .negative ⟨a j.val,G j⟩) : Nonempty (Source G) := by
  obtain ⟨x₁,x₂,x₃,hx₁,hx₂,hx₃,hxz,hxq⟩ := W.support_failure hp
  obtain ⟨y₁,y₂,y₃,hy₁,hy₂,hy₃,hyz,hyq⟩ := W.support_failure hn
  let T : Triple (G i) := ⟨x₁,x₂,x₃,hx₁,hx₂,hx₃⟩
  let U : Triple (G j) := ⟨y₁,y₂,y₃,hy₁,hy₂,hy₃⟩
  have htz : G i T.xor=0 := hxz
  have huz : G j U.xor=0 := hyz
  have htq : charge T.xor≤0 := by simpa [EOSign.value,T,Triple.xor] using hxq
  have huq : 0≤charge U.xor := by
    change -1*charge U.xor≤0 at hyq
    omega
  by_cases ht : charge T.xor=0
  · exact ⟨literal G i T hei htz ht⟩
  by_cases hu : charge U.xor=0
  · exact ⟨literal G j U hej huz hu⟩
  exact ⟨{
    copies := firstCopies U+secondCopies T
    labels := balancedLabels T U
    central := combined_central G i j _ _ hei hej
    hole := balanced_hole T U htz (by omega) (by omega) }⟩

def select (i j : Fin s) (hei : Signature.CentralSupport (G i))
    (hej : Signature.CentralSupport (G j))
    (hp : ¬W.Supports .positive ⟨a i.val,G i⟩)
    (hn : ¬W.Supports .negative ⟨a j.val,G j⟩) : Source G :=
  Classical.choice (exists_source G i j hei hej hp hn)

variable (D : Source G)

theorem source_eo : IsEO ⟨_,D.graph.denote⟩ := by
  obtain ⟨T,_,_⟩ := D.hole
  refine ⟨⟨weight T.first,?_⟩,D.central⟩
  by_contra h
  exact T.first_supported (D.central T.first (Ne.symm h))

theorem source_nonzero : D.graph.denote≠0 := by
  obtain ⟨T,_,_⟩ := D.hole
  intro h
  exact T.first_supported (congrFun h T.first)

theorem source_positive : 0<GeneralEONegativeTensorCore.arity (a:=a) D.labels := by
  obtain ⟨T,hz,_⟩ := D.hole
  by_contra hp
  have hn : GeneralEONegativeTensorCore.arity (a:=a) D.labels=0 := by omega
  have hx : T.first=T.xor := by
    funext i
    exact Fin.elim0 (Fin.cast hn i)
  exact T.first_supported (hx.symm ▸ hz)

theorem source_preprocessed : Preprocessed {⟨_,D.graph.denote⟩} := by
  intro g hg
  rcases Set.mem_singleton_iff.mp hg with rfl
  exact ⟨source_positive G D,source_nonzero G D⟩

theorem source_not_tract : ¬EOTract {⟨_,D.graph.denote⟩} := by
  intro h
  obtain ⟨_,_,sign,_,hs,_⟩ := h
  exact centralHole_not_supports D.hole sign (hs _ (by simp))

theorem source_preprocessed_negative : ¬EOTract (preprocess {⟨_,D.graph.denote⟩}) := by
  rw [preprocess_eq_self (source_preprocessed G D)]
  exact source_not_tract G D

/-- The actual paired restriction retains a support hole, so the same pairing
simultaneously fails both class choices. -/
theorem exists_bad_pairing : ∃p : OrientedPerfectPairing (GeneralEONegativeTensorCore.arity (a:=a) D.labels),
    ¬Affine (p.restrict D.graph.denote) ∧ ¬Product (p.restrict D.graph.denote) := by
  obtain ⟨T,hz,hq⟩ := D.hole
  exact ⟨GeneralEONegativePairing.pairing D.graph.denote D.central
      T.first_supported T.second_supported T.third_supported hq,
    GeneralEONegativePairing.pairing_bad D.graph.denote D.central
      T.first_supported T.second_supported T.third_supported hz hq⟩

abbrev controlled := GeneralEONegativeTensorAccess.controlled G D.labels
abbrev query := GeneralEONegativeTensorAccess.query (a:=a) D.labels

theorem query_resources (r : GeneralEONegativeTensorAccess.Input (a:=a) D.labels) :
    (query G D r).val.vertices.length=r.val.vertices.length*D.copies ∧
    (query G D r).val.edges.length=r.val.edges.length :=
  GeneralEONegativeTensorAccess.query_resources D.labels r

/-- Direct consumption of the already selected original negative pair. -/
def fromSelection (p : EONegativePairReduction.Selection G)
    (heo : ∀g∈preprocess (EONegativePairReduction.family G),IsEO g)
    (h : ¬W.Supports .positive (EONegativePairReduction.signature G p.first) ∧
      ¬W.Supports .negative (EONegativePairReduction.signature G p.second)) : Source G :=
  select G p.first p.second
    (heo _ ⟨⟨p.first,rfl⟩,p.first_kept⟩).2
    (heo _ ⟨⟨p.second,rfl⟩,p.second_kept⟩).2 h.1 h.2

/-- The complete original EO failure now has one of two produced outcomes:
an actual central-hole macro source, or literal bad pairings of kept original
labels. This does not replace either remaining hardness proof by a hypothesis. -/
theorem universal_dispatch
    (heo : ∀g∈preprocess (EONegativePairReduction.family G),IsEO g)
    (hbad : ¬EOTract (preprocess (EONegativePairReduction.family G))) :
    Nonempty (Source G) ∨ ∃i j : Fin s,
      EONegativePairReduction.Kept G i ∧ EONegativePairReduction.Kept G j ∧
      ∃p : OrientedPerfectPairing (a i.val),∃q : OrientedPerfectPairing (a j.val),
        ¬Affine (p.restrict (G i)) ∧ ¬Product (q.restrict (G j)) := by
  let p := EONegativePairReduction.choose G heo hbad
  rcases p.obstruction with hs|hc
  · exact Or.inl ⟨fromSelection G p heo hs⟩
  · obtain ⟨pa,hpa⟩ := W.pairing_failure hc.1
    obtain ⟨pp,hpp⟩ := W.pairing_failure hc.2
    exact Or.inr ⟨p.first,p.second,p.first_kept,p.second_kept,pa,pp,hpa,hpp⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeSupportSource
