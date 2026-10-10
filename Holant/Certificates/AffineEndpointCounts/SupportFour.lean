import Holant.Certificates.AffineReference.Source
import Holant.Kernel

/-! A.2(iii) with either original block chosen as I. The two actual native-X
wires close I-complement and keep the ordered I blocks of the original copies. -/
namespace Holant.Certificates.AffineEndpointCounts
noncomputable section
open Holant Holant.Tractable Holant.Certificates.AffineReference
open Holant.Certificates.FourthRootOdd Holant.Certificates.TwelveLoops
open Holant.EightVertex.ProductAnchor
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000

 def selectedPlaneTable (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (other : Bool) : Signature AlgebraicComplex 2 :=
  fun y=>planeTable h b (if other then ![y 1,y 0] else y)

 def selectedClosedPair (b : Fin 3) (other : Bool) : Fin 6 :=
  if other then initialPair b else complementaryPair b

 theorem support_four_two_copy_other (b : Fin 3) (A B C D : AlgebraicComplex) :
    twoCopy (blockTensor b A B C D) (initialPair b)=
      blockTensor 0 (2*A*C) (A*D+B*C) (A*D+B*C) (2*B*D) := by
  funext x
  fin_cases b <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [twoCopy,blockTensor,OnPlane,insertPair,firstHalf,secondHalf,
    portEquiv,portInverse,initialPair,blockPair,blockComplement,h0,h1,h2,h3]
  all_goals ring

 theorem selected_support_four_formula (h : Signature AlgebraicComplex 4)
    (b : Fin 3) (other : Bool) (hs : PlaneSupport h b) :
    let F:=selectedPlaneTable h b other
    twoCopyNative h (selectedClosedPair b other)=
      blockTensor 0 (2*F ![false,false]*F ![false,true])
        (F ![false,false]*F ![true,true]+F ![false,true]*F ![true,false])
        (F ![false,false]*F ![true,true]+F ![false,true]*F ![true,false])
        (2*F ![true,false]*F ![true,true]) := by
  cases other
  · dsimp [selectedPlaneTable,selectedClosedPair]
    conv_lhs => rw [twoCopyNative_eq,plane_reconstruction h b hs,support_four_two_copy]
  · dsimp [selectedPlaneTable,selectedClosedPair]
    conv_lhs => rw [twoCopyNative_eq,plane_reconstruction h b hs,support_four_two_copy_other]
    congr 1 <;> ring

 def tableMatrix (F : Signature AlgebraicComplex 2) : Kernel AlgebraicComplex :=
  fun a b=>F ![a,b]

 theorem fxft_table (F : Signature AlgebraicComplex 2) (a b : Bool) :
    Kernel.mul (Kernel.mul (tableMatrix F) Signature.disequality)
      (Kernel.transpose (tableMatrix F)) a b=
    if a then (if b then 2*F ![true,false]*F ![true,true]
      else F ![false,false]*F ![true,true]+F ![false,true]*F ![true,false])
    else (if b then F ![false,false]*F ![true,true]+F ![false,true]*F ![true,false]
      else 2*F ![false,false]*F ![false,true]) := by
  cases a <;> cases b <;>
    simp [Kernel.mul_apply,Kernel.transpose,tableMatrix,Signature.disequality] <;> ring

 theorem selected_output_logical_table (h : Signature AlgebraicComplex 4)
    (b : Fin 3) (other : Bool) (hs : PlaneSupport h b) (y : Fin 2 → Bool) :
    planeTable (twoCopyNative h (selectedClosedPair b other)) 0 y=
      Kernel.mul (Kernel.mul (tableMatrix (selectedPlaneTable h b other)) Signature.disequality)
        (Kernel.transpose (tableMatrix (selectedPlaneTable h b other))) (y 0) (y 1) := by
  rw [selected_support_four_formula h b other hs]
  unfold planeTable
  rw [blockTensor_chart,fxft_table]

 theorem selected_table_nonzero (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (other : Bool) (hs : PlaneSupport h b) (y : Fin 2 → Bool) : selectedPlaneTable h b other y≠0 :=
  planeTable_nonzero h b hs _

 theorem source_support_four_ordered (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (other : Bool) (ha : Affine h) (hs : PlaneSupport h b) :
    let F:=selectedPlaneTable h b other
    (F ![false,false]*F ![true,true]/(F ![false,true]*F ![true,false])=1 ∨
      F ![false,false]*F ![true,true]/(F ![false,true]*F ![true,false])= -1) ∧
    (F ![false,false]*F ![true,true]=F ![false,true]*F ![true,false] → TwoWeightedEqualities h) ∧
    (F ![false,false]*F ![true,true]= -(F ![false,true]*F ![true,false]) →
      PureEquality (twoCopyNative h (selectedClosedPair b other))) ∧
    Gadget.Realizes ({⟨4,h⟩} : SignatureFamily AlgebraicComplex) .disequality
      (twoCopyNative h (selectedClosedPair b other)) := by
  dsimp only
  refine ⟨?_,?_,?_,twoCopy_realizes h _⟩
  · cases other <;> simpa [selectedPlaneTable,mul_comm] using plane_cross_ratio h b ha hs
  · intro hp
    apply plane_positive_factor h b hs
    cases other <;> simpa [selectedPlaneTable,mul_comm] using hp
  · intro hn
    rw [selected_support_four_formula h b other hs]
    have hz : selectedPlaneTable h b other ![false,false]*selectedPlaneTable h b other ![true,true]+
      selectedPlaneTable h b other ![false,true]*selectedPlaneTable h b other ![true,false]=0 := by
      linear_combination hn
    rw [hz]
    apply diagonal_block_pure
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (selected_table_nonzero h b other hs _))
        (selected_table_nonzero h b other hs _)
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (selected_table_nonzero h b other hs _))
        (selected_table_nonzero h b other hs _)


 def selectedBlock (b : Fin 3) (other : Bool) : Finset (Fin 4) :=
  if other then {(blockComplement b).1,(blockComplement b).2}
    else {(blockPair b).1,(blockPair b).2}

 theorem all_original_blocks : ∀I : Finset (Fin 4),I.card=2 →
    ∃b : Fin 3,∃other : Bool,I=selectedBlock b other := by decide

 theorem selected_table_original_values (h : Signature AlgebraicComplex 4)
    (b : Fin 3) (other : Bool) :
    selectedPlaneTable h b other ![false,false]=h (fun _=>false) ∧
    selectedPlaneTable h b other ![true,true]=h (fun _=>true) ∧
    selectedPlaneTable h b other ![true,false]=h (fun i=>decide (i∈selectedBlock b other)) ∧
    selectedPlaneTable h b other ![false,true]=h (fun i=>decide (i∉selectedBlock b other)) := by
  fin_cases b <;> cases other <;>
    simp [selectedPlaneTable,planeTable,planeChart,selectedBlock,blockPair,blockComplement]
  all_goals repeat' apply And.intro
  all_goals apply congrArg h; funext i; fin_cases i <;> rfl

 theorem selected_network_counts (h : Signature AlgebraicComplex 4) (b : Fin 3) (other : Bool) :
    (twoCopyNetwork h (selectedClosedPair b other)).shape.vertices=2 ∧
    (twoCopyNetwork h (selectedClosedPair b other)).shape.edges=2 ∧
    (twoCopyNetwork h (selectedClosedPair b other)).denote=
      twoCopyNative h (selectedClosedPair b other) := by
  refine ⟨rfl,rfl,?_⟩
  rw [twoCopyNetwork_denote,twoCopyNative_eq]

/-- Complete support-four clause with both original block roles, exact matrix
formula, two original copies/two native-X edges, and actual output realization. -/
 def SourceA2SupportFour : Prop :=
  (∀I : Finset (Fin 4),I.card=2 → ∃b : Fin 3,∃other : Bool,I=selectedBlock b other) ∧
  ∀(h : Signature AlgebraicComplex 4),Affine h → ∀(b : Fin 3) (other : Bool),PlaneSupport h b →
    let F:=selectedPlaneTable h b other
    (∀y : Fin 2 → Bool,planeTable (twoCopyNative h (selectedClosedPair b other)) 0 y=
      Kernel.mul (Kernel.mul (tableMatrix F) Signature.disequality)
        (Kernel.transpose (tableMatrix F)) (y 0) (y 1)) ∧
    (F ![false,false]*F ![true,true]/(F ![false,true]*F ![true,false])=1 ∨
      F ![false,false]*F ![true,true]/(F ![false,true]*F ![true,false])= -1) ∧
    (F ![false,false]*F ![true,true]=F ![false,true]*F ![true,false] → TwoWeightedEqualities h) ∧
    (F ![false,false]*F ![true,true]= -(F ![false,true]*F ![true,false]) →
      PureEquality (twoCopyNative h (selectedClosedPair b other))) ∧
    Gadget.Realizes ({⟨4,h⟩} : SignatureFamily AlgebraicComplex) .disequality
      (twoCopyNative h (selectedClosedPair b other)) ∧
    (twoCopyNetwork h (selectedClosedPair b other)).shape.vertices=2 ∧
    (twoCopyNetwork h (selectedClosedPair b other)).shape.edges=2 ∧
    (twoCopyNetwork h (selectedClosedPair b other)).denote=twoCopyNative h (selectedClosedPair b other)

 theorem source_A2_support_four : SourceA2SupportFour := by
  refine ⟨all_original_blocks,?_⟩
  intro h ha b other hs
  obtain ⟨hc,hp,hn,hr⟩ := source_support_four_ordered h b other ha hs
  exact ⟨selected_output_logical_table h b other hs,hc,hp,hn,hr,selected_network_counts h b other⟩

end
end Holant.Certificates.AffineEndpointCounts
