import Holant.Proofs.Closure.ClosureSixPortFourPositions

/-! NEW UNVERIFIED exact Boolean normalization laws. Coefficients and actual
networks are not changed here; these finite equalities record both ordered-edge
orientations and every bit-flip tag for the literal four-flat support. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fixed_coordinate_gauge (reverse : Bool) (x y d e a : Bool) :
    ((if reverse then x^^d else y^^e) =
      ((if reverse then y^^e else x^^d) ^^ a)) ↔
      y = (x ^^ ((a^^d)^^e)) := by
  cases reverse <;> cases x <;> cases y <;> cases d <;> cases e <;> cases a <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem varying_coordinate_gauge (reverse : Bool) (x y d e o z b : Bool) :
    (((if reverse then y^^e else x^^d) = (o^^z)) ∧
      ((if reverse then x^^d else y^^e) = ((o^^z)^^b))) ↔
      (x = (((o ^^ (if reverse then b else false)) ^^ d) ^^ z) ∧
        y = ((((o ^^ (if reverse then b else false)) ^^ d) ^^ z) ^^ ((b^^d)^^e))) := by
  cases reverse <;> cases x <;> cases y <;> cases d <;> cases e <;>
    cases o <;> cases z <;> cases b <;> decide

def firstFlatSupport : Finset (Word 6) :=
  Finset.univ.image (fun v : Bool×Bool => firstFlat v.1 v.2)

def secondFlatSupport (edge : Fin 6) (a b o : Bool) : Finset (Word 6) :=
  Finset.univ.image (fun v : Bool×Bool => secondFlat edge a b o v.1 v.2)

def secondFlatCondition (edge : Fin 6) (a b o : Bool) (w : Word 6) : Prop :=
  w 1 = !(w 0) ∧
  w (fixedPositions edge 1).succ.succ = (w (fixedPositions edge 0).succ.succ ^^ a) ∧
  w (varyingPositions edge 0).succ.succ = (o^^w 0) ∧
  w (varyingPositions edge 1).succ.succ = ((o^^w 0)^^b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem firstFlat_support_iff (w : Word 6) :
    w ∈ firstFlatSupport ↔ w 1=w 0 ∧ w 3=w 2 ∧ w 4=w 0 ∧ w 5=w 0 := by
  revert w
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem secondFlat_support_iff (edge : Fin 6) (a b o : Bool) (w : Word 6) :
    w ∈ secondFlatSupport edge a b o ↔ secondFlatCondition edge a b o w := by
  revert w
  fin_cases edge <;> cases a <;> cases b <;> cases o <;>
    unfold secondFlatCondition <;> decide

theorem flatSupport_partition (edge : Fin 6) (a b o : Bool) :
    flatSupport edge a b o = firstFlatSupport ∪ secondFlatSupport edge a b o := by
  ext x
  simp only [flatSupport,firstFlatSupport,secondFlatSupport,Finset.mem_image,Finset.mem_univ,
    true_and,Finset.mem_union]
  constructor
  · rintro ⟨⟨sector,z,w⟩,equal⟩
    cases sector
    · exact Or.inl ⟨⟨z,w⟩,equal⟩
    · exact Or.inr ⟨⟨z,w⟩,equal⟩
  · rintro (⟨⟨z,w⟩,equal⟩ | ⟨⟨z,w⟩,equal⟩)
    · exact ⟨⟨false,z,w⟩,equal⟩
    · exact ⟨⟨true,z,w⟩,equal⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
