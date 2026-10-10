import Holant.Pauli.ExoticKlein.SixPortLocalAction

/-! Local matrix actions on actual disjoint matching factors, preserving the
original edge and endpoint order. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
variable {P : Type*} [DecidableEq P] {r : ℕ}

 def binaryTensor (M : Matching P r) (factors : Fin r → Mat) : Tensor ℂ P :=
  fun x => ∏ e, factors e (x (M.ports (e,false))) (x (M.ports (e,true)))

 theorem binaryTensor_update_factor (M : Matching P r) (factors : Fin r → Mat)
    (e : Fin r) (A : Mat) (x : P → Bool) :
    binaryTensor M (Function.update factors e A) x =
      A (x (M.ports (e,false))) (x (M.ports (e,true)))*
        ∏ j ∈ Finset.univ.erase e, factors j (x (M.ports (j,false))) (x (M.ports (j,true))) := by
  unfold binaryTensor
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

 theorem binaryTensor_update_port (M : Matching P r) (factors : Fin r → Mat)
    (e : Fin r) (b : Bool) (x : P → Bool) (u : Bool) :
    binaryTensor M factors (Function.update x (M.ports (e,b)) u) =
      (if b then factors e (x (M.ports (e,false))) u else factors e u (x (M.ports (e,true))))*
        ∏ j ∈ Finset.univ.erase e, factors j (x (M.ports (j,false))) (x (M.ports (j,true))) := by
  unfold binaryTensor
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  have hends : M.ports (e,false) ≠ M.ports (e,true) := by
    intro h
    have hh := congrArg Prod.snd (M.ports.injective h)
    contradiction
  congr 1
  · cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Function.update_self,
      Function.update_of_ne hends,Function.update_of_ne hends.symm]
  · apply Finset.prod_congr rfl
    intro j hj
    have hne (c : Bool) : M.ports (j,c) ≠ M.ports (e,b) := by
      intro h
      exact (Finset.mem_erase.mp hj).1 (congrArg Prod.fst (M.ports.injective h))
    rw [Function.update_of_ne (hne false),Function.update_of_ne (hne true)]

 theorem localMatrix_binary_first (M : Matching P r) (factors : Fin r → Mat) (e : Fin r) (A : Mat) :
    localMatrix (M.ports (e,false)) A (binaryTensor M factors) =
      binaryTensor M (Function.update factors e (Kernel.mul A (factors e))) := by
  funext x
  rw [binaryTensor_update_factor]
  simp only [localMatrix,binaryTensor_update_port,Fintype.sum_bool,Kernel.mul_apply,Bool.false_eq_true,ite_false]
  ring

 theorem localMatrix_binary_second (M : Matching P r) (factors : Fin r → Mat) (e : Fin r) (A : Mat) :
    localMatrix (M.ports (e,true)) A (binaryTensor M factors) =
      binaryTensor M (Function.update factors e (Kernel.mul (factors e) (Kernel.transpose A))) := by
  funext x
  rw [binaryTensor_update_factor]
  simp only [localMatrix,binaryTensor_update_port,Fintype.sum_bool,Kernel.mul_apply,Kernel.transpose_apply,ite_true]
  ring

 theorem binaryTensor_update_scale (M : Matching P r) (factors : Fin r → Mat) (e : Fin r) (A : Mat) (s : ℂ) :
    binaryTensor M (Function.update factors e (scale s A)) =
      fun x => s*binaryTensor M (Function.update factors e A) x := by
  funext x
  rw [binaryTensor_update_factor,binaryTensor_update_factor]
  simp only [scale]
  ring

 theorem label_update_factors (labels : Fin r → Label) (e : Fin r) (a : Label) :
    Function.update (fun j => E (labels j)) e (E a) = fun j => E (Function.update labels e a j) := by
  funext j
  by_cases hj : j = e <;> simp [hj]

 theorem localAction_matching_first (M : Matching P r) (labels : Fin r → Label) (e : Fin r) (a : Label) :
    localAction (M.ports (e,false)) a (M.tensor labels) =
      fun x => omega a (labels e)*M.tensor (Function.update labels e (a+labels e)) x := by
  change localMatrix _ (E a) (binaryTensor M (fun j => E (labels j))) = _
  rw [localMatrix_binary_first,fusion,binaryTensor_update_scale,label_update_factors]
  rfl

 theorem fusion_transpose_right (a b : Label) :
    Kernel.mul (E b) (Kernel.transpose (E a)) =
      scale (transposeScalar a*omega b (theta a)) (E (b+theta a)) := by
  rw [transpose_E]
  funext x y
  have hf := congrFun (congrFun (fusion b (theta a)) x) y
  simp only [Kernel.mul_apply,scale] at hf ⊢
  calc
    _ = transposeScalar a*(E b x false*E (theta a) false y+E b x true*E (theta a) true y) := by ring
    _ = _ := by rw [hf]; ring

 theorem localAction_matching_second (M : Matching P r) (labels : Fin r → Label) (e : Fin r) (a : Label) :
    localAction (M.ports (e,true)) a (M.tensor labels) =
      fun x => (transposeScalar a*omega (labels e) (theta a))*
        M.tensor (Function.update labels e (labels e+theta a)) x := by
  change localMatrix _ (E a) (binaryTensor M (fun j => E (labels j))) = _
  rw [localMatrix_binary_second,fusion_transpose_right,binaryTensor_update_scale,label_update_factors]
  rfl

 theorem localAction_matching (M : Matching P r) (labels : Fin r → Label) (p : P) (a : Label) :
    ∃ labels' : Fin r → Label, ∃ s : ℂ, s ≠ 0 ∧
      localAction p a (M.tensor labels) = fun x => s*M.tensor labels' x := by
  obtain ⟨⟨e,b⟩,rfl⟩ := M.ports.surjective p
  cases b
  · exact ⟨Function.update labels e (a+labels e),omega a (labels e),omega_ne_zero _ _,localAction_matching_first M labels e a⟩
  · exact ⟨Function.update labels e (labels e+theta a),transposeScalar a*omega (labels e) (theta a),
      mul_ne_zero (transposeScalar_ne_zero _) (omega_ne_zero _ _),localAction_matching_second M labels e a⟩

 theorem onMatching_localAction (h : Tensor ℂ P) (hh : OnMatching h) (p : P) (a : Label) :
    OnMatching (localAction p a h) := by
  rcases hh with rfl | ⟨M,labels,s,hs,rfl⟩
  · left; exact localMatrix_zero p (E a)
  · obtain ⟨labels',t,ht,he⟩ := localAction_matching M labels p a
    right
    refine ⟨M,labels',s*t,mul_ne_zero hs ht,?_⟩
    unfold localAction at he ⊢
    rw [localMatrix_scale_tensor,he]
    funext x
    ring

end
end Holant.Pauli.ExoticKlein.SixPort
