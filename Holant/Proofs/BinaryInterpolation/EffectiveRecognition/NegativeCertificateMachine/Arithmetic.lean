import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Codec


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine
open Holant.LocalDrafts.EffectiveAlgebraic
open CommonFieldMachine

def addExponent (a b : Exponent) : Exponent :=
  Coordinates.tab a.length (fun i => a.getD i 0+b.getD i 0)
def termProduct (c : List ℚ) (t u : Term) : Term :=
  (addExponent t.1 u.1,Coordinates.mul c t.2 u.2)
def mul (c : List ℚ) (p q : Poly) : Poly := p.flatMap (fun t => q.map (termProduct c t))
def coefficient (d : ℕ) (p : Poly) (a : Exponent) : List ℚ :=
  Coordinates.sum d (p.map (fun t => if t.1=a then t.2 else Coordinates.zero d))
def zeroCoefficients (d : ℕ) (p : Poly) : Bool :=
  p.all (fun t => Coordinates.isZero (coefficient d p t.1))
def materialize (a : List (List ℚ)) (e : Equation) : Poly :=
  e.map (fun t => (t.2,a.getD t.1 []))
def coordinates (c : List ℚ) (e : List RationalPolynomialCode) := e.map (Coordinates.reduce c)
def defect (n : ℕ) (c : List ℚ) (e : List RationalPolynomialCode) (S : System) (H : List Poly) : Poly :=
  (Coordinates.tab S.length (fun i =>
    mul c (H.getD i []) (materialize (coordinates c e) (S.getD i [])))).flatten ++
      [(List.replicate n 0,Coordinates.scale (-1) (Coordinates.unit c.length))]

theorem getD_ofFn {A : Type} {n : ℕ} (v : Fin n → A) (i : Fin n) (default : A) :
    (List.ofFn v).getD i.val default = v i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

theorem exponent_faithful {n : ℕ} (a b : Fin n → ℕ) : List.ofFn a=List.ofFn b ↔ a=b := by
  constructor
  · intro h; funext i
    have hi := congrArg (fun xs : List ℕ => xs.getD i.val 0) h
    simpa only [getD_ofFn] using hi
  · rintro rfl; rfl

theorem termWire_injective {n d : ℕ} : Function.Injective (termWire (n:=n) (d:=d)) := by
  intro t u h
  apply Prod.ext
  · exact (exponent_faithful t.1 u.1).mp (congrArg Prod.fst h)
  · funext i
    have hi := congrArg (fun v : Term => v.2.getD i.val 0) h
    simpa only [termWire,getD_ofFn] using hi

theorem polyWire_injective {n d : ℕ} : Function.Injective (polyWire (n:=n) (d:=d)) :=
  termWire_injective.list_map

theorem sourceTermWire_injective {m n : ℕ} :
    Function.Injective (sourceTermWire (m:=m) (n:=n)) := by
  intro t u h
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact (exponent_faithful t.2 u.2).mp (congrArg Prod.snd h)

theorem systemWire_injective {m n : ℕ} : Function.Injective (systemWire (m:=m) (n:=n)) :=
  sourceTermWire_injective.list_map.list_map

/-- The two lists are indexed by the same original position, even when two
equations or two multipliers happen to have identical literal contents. -/
theorem original_equation_at {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (r : NullstellensatzSearch.Candidate m n S.length)
    (i : Fin S.length) :
    (fromCandidate target S r).equations.getD i.val [] = equationWire (S.get i) := by
  change (systemWire S).getD i.val [] = _
  have hs : systemWire S = List.ofFn (fun j : Fin S.length => equationWire (S.get j)) := by
    conv_lhs => rw [systemWire,← List.ofFn_get S,List.map_ofFn]
    rfl
  rw [hs,getD_ofFn]

theorem original_multiplier_at {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (r : NullstellensatzSearch.Candidate m n S.length)
    (i : Fin S.length) :
    (fromCandidate target S r).multipliers.getD i.val [] = polyWire (r.2.multiplier i) := by
  exact getD_ofFn (fun j => polyWire (r.2.multiplier j)) i []

theorem addExponent_ofFn {n : ℕ} (a b : Fin n → ℕ) :
    addExponent (List.ofFn a) (List.ofFn b) = List.ofFn (a+b) := by
  simp only [addExponent,List.length_ofFn,Coordinates.tab_ofFn,getD_ofFn]
  rfl

theorem termProduct_wire {n d : ℕ} (c : PowerArithmetic.Vector d)
    (t u : Sparse.Term n (d+1)) :
    termProduct (List.ofFn c) (termWire t) (termWire u) =
      termWire (t.1+u.1,(PowerArithmetic.data c).mulCode t.2 u.2) := by
  simp only [termProduct,termWire,addExponent_ofFn,Coordinates.mul_ofFn]

theorem mul_wire {n d : ℕ} (c : PowerArithmetic.Vector d) (p q : NullstellensatzSearch.Poly n d) :
    mul (List.ofFn c) (polyWire p) (polyWire q) = polyWire (Sparse.mul (PowerArithmetic.data c) p q) := by
  simp only [mul,polyWire,Sparse.mul,Sparse.termMul,List.flatMap_map,List.map_flatMap,List.map_map,
    Function.comp_def,termProduct_wire]

theorem sum_wire {d : ℕ} (vs : List (Fin d → ℚ)) :
    Coordinates.sum d (vs.map List.ofFn) = List.ofFn vs.sum := by
  induction vs with
  | nil => exact Coordinates.zero_ofFn d
  | cons v vs ih =>
    rw [List.map_cons,Coordinates.sum_cons,ih,Coordinates.add_ofFn,List.sum_cons]

/-- General coefficient theorem: all repetitions are collected before testing. -/
theorem coefficient_wire {n d : ℕ} (p : Sparse.Poly n d) (a : Sparse.Exponent n) :
    coefficient d (polyWire p) (List.ofFn a) = List.ofFn (Sparse.coefficient p a) := by
  induction p with
  | nil => exact Coordinates.zero_ofFn d
  | cons t p ih =>
    rw [Sparse.coefficient_cons]
    rw [coefficient,polyWire,List.map_cons,List.map_cons,Coordinates.sum_cons]
    change Coordinates.add d
      (if List.ofFn t.1=List.ofFn a then List.ofFn t.2 else Coordinates.zero d)
      (coefficient d (polyWire p) (List.ofFn a)) = _
    rw [ih]
    by_cases h : t.1=a
    · simp [h,Coordinates.add_ofFn]
    · simp only [exponent_faithful,h,ite_false,Coordinates.zero_ofFn,Coordinates.add_ofFn]
      rfl

theorem zeroCoefficients_wire {n d : ℕ} (p : NullstellensatzSearch.Poly n d) :
    zeroCoefficients (d+1) (polyWire p) = NullstellensatzSearch.zeroCoefficients p := by
  simp only [zeroCoefficients,polyWire,List.all_map,NullstellensatzSearch.zeroCoefficients]
  apply congrArg (fun f => p.all f)
  funext t
  change Coordinates.isZero (coefficient (d+1) (polyWire p) (List.ofFn t.1)) = _
  rw [coefficient_wire,Coordinates.isZero_ofFn]

/-- Nonzero literal coefficients may cancel. Acceptance is derived from the
collected coefficient theorem, not from testing either record in isolation. -/
theorem opposite_terms_cancel {n d : ℕ} (a : Sparse.Exponent n) (v : PowerArithmetic.Vector d) :
    zeroCoefficients (d+1) (polyWire [(a,v),(a,-v)]) = true := by
  rw [zeroCoefficients_wire,NullstellensatzSearch.zeroCoefficients_iff]
  intro b
  by_cases h : a=b <;> simp [Sparse.coefficient_cons,h]

theorem coordinates_ofFn {d m : ℕ} (c : PowerArithmetic.Vector d)
    (e : Fin m → RationalPolynomialCode) :
    coordinates (List.ofFn c) (List.ofFn e) =
      List.ofFn (fun i => List.ofFn (CommonFieldCheck.familyCoordinates c e i)) := by
  simp only [coordinates,List.map_ofFn,Function.comp_def,Coordinates.reduce_ofFn,CommonFieldCheck.familyCoordinates]

theorem materialize_wire {d m n : ℕ} (a : Fin m → PowerArithmetic.Vector d)
    (e : EncodedSystem.Equation m n) :
    materialize (List.ofFn (fun i => List.ofFn (a i))) (equationWire e) =
      polyWire (NullstellensatzSearch.materialize a e) := by
  simp [materialize,equationWire,sourceTermWire,polyWire,termWire,
    NullstellensatzSearch.materialize,List.map_map,Function.comp_def,getD_ofFn]

theorem defect_wire {d m n : ℕ} (c : PowerArithmetic.Vector d)
    (e : Fin m → RationalPolynomialCode) (S : EncodedSystem.System m n)
    (H : Fin S.length → NullstellensatzSearch.Poly n d) :
    defect n (List.ofFn c) (List.ofFn e) (systemWire S) (List.ofFn (fun i => polyWire (H i))) =
      polyWire (NullstellensatzSearch.defect c e S H) := by
  have hs : systemWire S = List.ofFn (fun i : Fin S.length => equationWire (S.get i)) := by
    conv_lhs => rw [systemWire,← List.ofFn_get S,List.map_ofFn]
    rfl
  have rows : Coordinates.tab (systemWire S).length (fun i =>
      mul (List.ofFn c) ((List.ofFn (fun j => polyWire (H j))).getD i [])
        (materialize (coordinates (List.ofFn c) (List.ofFn e)) ((systemWire S).getD i []))) =
      List.ofFn (fun i : Fin S.length => polyWire (Sparse.mul (PowerArithmetic.data c)
        (H i) (NullstellensatzSearch.materialize (CommonFieldCheck.familyCoordinates c e) (S.get i)))) := by
    rw [hs]
    simp only [List.length_ofFn,Coordinates.tab_ofFn,getD_ofFn,coordinates_ofFn,
      materialize_wire,mul_wire]
  have unit : (List.replicate n 0,Coordinates.scale (-1) (Coordinates.unit (d+1))) =
      termWire (n := n) (0,-(PowerArithmetic.data c).unitCode) := by
    rw [Coordinates.unit_ofFn,Coordinates.scale_ofFn]
    simp only [termWire,PowerArithmetic.data,neg_one_smul]
    congr 1
    change List.replicate n 0 = List.ofFn (fun _ : Fin n => 0)
    rw [List.ofFn_const]
  unfold defect
  rw [rows,List.length_ofFn,unit]
  simp only [NullstellensatzSearch.defect,Sparse.sub,Sparse.add,Sparse.one,Sparse.neg,
    polyWire,List.map_append,List.map_flatten,List.map_ofFn,List.map_cons,List.map_nil,
    Function.comp_def]


end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine
