import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticFourierRecipe

/-! The mixed recipe's semantic coefficient is the literal typed row product;
its private-variable trace retains the exact cubic scale and literal pins. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticFourierRecipeSemantics
open Holant Holant.Tractable
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open OrdinaryNegativeOcticFourierRecipe
open scoped BigOperators
namespace S
export StableHigherCurrentOrdinarySquare (rowValue weight extend)
end S
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue (coefficient)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {K : Type} [CommRing K]

theorem node_value (H : (j : Fin 5)→Signature K (targetArity j.val))
    (i : Fin 4) (r : Factor) (hr : r∈rows i) (x : Fin (expanded i.val) → Bool) :
    H (node i r hr).1 (fun j=>Sum.elim id x ((node i r hr).2 j))=
      S.rowValue H r (S.extend x) := by
  unfold StableHigherCurrentOrdinarySquare.rowValue
  rw [dif_pos (rows_valid i r hr).1]
  change H ⟨r.1,(rows_valid i r hr).1⟩ _=H ⟨r.1,(rows_valid i r hr).1⟩ _
  congr 1
  funext j
  have hj : j.val<r.2.length := Nat.lt_of_lt_of_eq j.isLt (rows_valid i r hr).2.1.symm
  have hp : r.2.getD j.val 0<expanded i.val := by
    rw [List.getD_eq_getElem _ _ hj]
    exact (rows_valid i r hr).2.2 _ (List.getElem_mem hj)
  have hp2 : r.2[j.val] < expanded i.val := by
    simpa only [List.getD_eq_getElem _ _ hj] using hp
  simp only [node,Sum.elim_inr,StableHigherCurrentOrdinarySquare.extend,
    List.getD_eq_getElem _ _ hj,List.get_eq_getElem,dif_pos hp2]

theorem coefficient_rows (H : (j : Fin 5)→Signature K (targetArity j.val))
    (i : Fin 4) (x : Fin (expanded i.val) → Bool) :
    D.coefficient H recipe i x=S.weight H (rows i) (S.extend x) := by
  unfold OrdinaryNegativeMixedBlockData.coefficient
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient
    recipe
  simp only [List.map_map,Function.comp_def]
  calc
    _ = (((rows i).attach).map (fun r=>S.rowValue H r.val (S.extend x))).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro r _
      exact node_value H i r.val r.property x
    _ = _ := by
      exact congrArg List.prod (List.attach_map_val
        (l:=rows i) (f:=fun r=>S.rowValue H r (S.extend x)))

/-- Actual private words are in bijection with all54-address words whose
three external ports are fixed. -/
def privateWords (x : Fin 3 → Bool) : (Fin 51 → Bool) ≃
    OrdinaryNegativeOcticParityFourierAssignments.Words x where
  toFun y := ⟨fun i=>Fin.addCases (m:=3) (n:=51) x y i,fun i=>by
    change Fin.addCases x y (Fin.castAdd 51 i)=x i
    simp⟩
  invFun w j := w.val (Fin.natAdd 3 j)
  left_inv y := by funext j; simp
  right_inv w := by
    apply Subtype.ext
    funext i
    refine Fin.addCases (m:=3) (n:=51) (fun j=>?_) (fun j=>?_) i
    · simp only [Fin.addCases_left]
      exact (w.property j).symm
    · simp


theorem fourier_row (z : K) (r : Factor) (hr : r.1<3) (w : ℕ→Bool) :
    S.rowValue (table z) r w=
      S.rowValue (OrdinaryNegativeOcticParityFourierTyped.table z) r w := by
  rcases r with ⟨j,scope⟩
  interval_cases j
  · rfl
  · rfl
  · change (if w (scope.getD 0 0)=false then (1 : K) else 0)=
      (if w (scope.getD 0 0) then 0 else 1)
    cases w (scope.getD 0 0) <;> rfl

theorem fourier_weight (z : K) (w : ℕ→Bool) :
    S.weight (table z) F.factors w=
      S.weight (OrdinaryNegativeOcticParityFourierTyped.table z) F.factors w := by
  unfold StableHigherCurrentOrdinarySquare.weight
  congr 1
  apply List.map_congr_left
  intro r hr
  exact fourier_row z r (OrdinaryNegativeOcticParityFourier.all_addresses_valid r hr).1 w

theorem cubic_trace (z : K) (hfour : z^4= -1) (x : Fin 3→Bool) :
    trace z 0 x=2^25*OrdinaryNegativeCubicCore.cubic x := by
  unfold trace
  simp_rw [coefficient_rows]
  change (∑y : Fin 51→Bool,S.weight (table z) F.factors (S.extend (Fin.addCases x y)))=_
  simp_rw [fourier_weight]
  rw [show (∑y : Fin 51→Bool,S.weight (OrdinaryNegativeOcticParityFourierTyped.table z)
      F.factors (S.extend (Fin.addCases x y)))=
      OrdinaryNegativeOcticParityFourierTyped.conditionalValue z x from
    (privateWords x).sum_comp (fun w=>S.weight (OrdinaryNegativeOcticParityFourierTyped.table z)
      F.factors (S.extend w.val))]
  exact OrdinaryNegativeOcticParityFourierTyped.conditional_cubic z hfour x

private theorem product_flatMap {α : Type*} (xs : List α) (f : α→List K) :
    (xs.flatMap f).prod=(xs.map (fun x=>(f x).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,List.prod_append,List.map_cons,List.prod_cons,ih]

theorem extend_old {n k : ℕ} (x : Fin n→Bool) (y : Fin k→Bool) (i : Fin n) :
    S.extend (Fin.addCases x y) i.val=x i := by
  unfold StableHigherCurrentOrdinarySquare.extend
  rw [dif_pos (show i.val<n+k by omega)]
  change Fin.addCases x y (Fin.castAdd k i)=x i
  simp

theorem extend_new {n k : ℕ} (x : Fin n→Bool) (y : Fin k→Bool) (i : Fin k) :
    S.extend (Fin.addCases x y) (n+i.val)=y i := by
  unfold StableHigherCurrentOrdinarySquare.extend
  rw [dif_pos (show n+i.val<n+k by omega)]
  change Fin.addCases x y (Fin.natAdd n i)=y i
  simp

theorem pin_row (z : K) (j : ℕ) (w : ℕ→Bool) :
    S.rowValue (table z) (2,[j]) w=if w j then 0 else 1 := by
  cases h : w j <;> simp [StableHigherCurrentOrdinarySquare.rowValue,table,
    Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin,h]

theorem old_row (z : K) (i : Fin 4) (hi : i.val≠0)
    (x : Fin (P.sourceArity i.val)→Bool) (y : Fin 51→Bool) :
    S.rowValue (table z) (oldLabel i,List.range (P.sourceArity i.val))
      (S.extend (Fin.addCases x y))=P.sourceRows i x := by
  fin_cases i
  · contradiction
  · change Holant.EightVertex.ProductAnchor.equalityFour _=
      Holant.EightVertex.ProductAnchor.equalityFour x
    congr 1
    funext j
    have hj : j.val<4 := j.isLt
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_range,OrdinaryNegativePhaseBundleRaw.sourceArity] using hj),List.getElem_range]
    exact extend_old x y j
  · change (Fin 1→Bool) at x
    change (if S.extend (Fin.addCases x y) 0=false then (1 : K) else 0)=
      (if x 0=false then 1 else 0)
    rw [show S.extend (Fin.addCases x y) 0=x 0 from extend_old x y 0]
  · change (Fin 1→Bool) at x
    change (if S.extend (Fin.addCases x y) 0=true then (1 : K) else 0)=
      (if x 0=true then 1 else 0)
    rw [show S.extend (Fin.addCases x y) 0=x 0 from extend_old x y 0]

theorem old_row_idempotent (i : Fin 4) (hi : i.val≠0)
    (x : Fin (P.sourceArity i.val)→Bool) :
    P.sourceRows (K:=K) i x*P.sourceRows i x=P.sourceRows i x := by
  fin_cases i
  · contradiction
  · simp only [OrdinaryNegativePhaseBundleRaw.sourceRows,Holant.EightVertex.ProductAnchor.equalityFour]
    split_ifs <;> simp
  · simp only [OrdinaryNegativePhaseBundleRaw.sourceRows,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin]
    split_ifs <;> simp
  · simp only [OrdinaryNegativePhaseBundleRaw.sourceRows,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin]
    split_ifs <;> simp


theorem private_pins (z : K) {n : ℕ} (x : Fin n→Bool) (y : Fin 51→Bool) :
    S.weight (table z) ((List.range 51).flatMap (fun j=>[(2,[n+j]),(2,[n+j])]))
      (S.extend (Fin.addCases x y))=if y=(fun _=>false) then 1 else 0 := by
  classical
  have hr : List.range 51=(List.finRange 51).map Fin.val := by decide
  unfold StableHigherCurrentOrdinarySquare.weight
  rw [hr,List.flatMap_map,List.map_flatMap,product_flatMap]
  simp only [Function.comp_def,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
    pin_row,extend_new]
  have hs (j : Fin 51) : (if y j then (0 : K) else 1)*(if y j then 0 else 1)=
      if y j=false then 1 else 0 := by cases y j <;> simp
  simp_rw [hs]
  rw [←List.ofFn_eq_map,List.prod_ofFn,Fintype.prod_boole]
  simp only [funext_iff]
  split_ifs <;> rfl

theorem other_coefficient (z : K) (i : Fin 4) (hi : i.val≠0)
    (x : Fin (P.sourceArity i.val)→Bool) (y : Fin 51→Bool) :
    D.coefficient (table z) recipe i (Fin.addCases x y)=
      P.sourceRows i x*(if y=(fun _=>false) then 1 else 0) := by
  rw [coefficient_rows]
  simp only [rows,hi,ite_false,otherRows]
  change S.weight (table z) _ (S.extend (Fin.addCases x y))=_
  rw [show ∀(rs ss : List Factor) (w : ℕ→Bool), S.weight (table z) (rs++ss) w=
    S.weight (table z) rs w*S.weight (table z) ss w from fun rs ss w=>by
      simp only [StableHigherCurrentOrdinarySquare.weight,List.map_append,List.prod_append]]
  simp only [StableHigherCurrentOrdinarySquare.weight,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,mul_one,old_row z i hi,old_row_idempotent i hi]
  rw [←StableHigherCurrentOrdinarySquare.weight,private_pins]

theorem other_trace (z : K) (i : Fin 4) (hi : i.val≠0)
    (x : Fin (P.sourceArity i.val)→Bool) : trace z i x=P.sourceRows i x := by
  classical
  unfold trace
  simp_rw [other_coefficient z i hi]
  simp

theorem trace_exact (z : K) (hfour : z^4= -1) (i : Fin 4)
    (x : Fin (P.sourceArity i.val)→Bool) :
    trace z i x=(if i.val=0 then 2^25 else 1)*P.sourceRows i x := by
  by_cases hi : i.val=0
  · have he : i=0 := Fin.ext hi
    subst i
    simpa only [Fin.val_zero,ite_true,OrdinaryNegativePhaseBundleRaw.sourceRows] using cubic_trace z hfour x
  · simpa only [hi,ite_false,one_mul] using other_trace z i hi x


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticFourierRecipeSemantics
end
