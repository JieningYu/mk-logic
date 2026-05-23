axiom Class : Type

variable {x y z w : Class}

axiom In : Class → Class → Prop
axiom Classify : (Class → Prop) → Class

instance : Membership Class Class where mem := In

@[ext] axiom Class.eq : (∀ z, z ∈ x ↔ z ∈ y) → x = y

abbrev Ensemble (x : Class) := ∃ (y : Class), x ∈ y

@[simp] axiom Class.classify {P : Class → Prop} : x ∈ Classify P ↔ (Ensemble x) ∧ (P x)

def Ensemble.intro (p : x ∈ y) : Ensemble x := Exists.intro y p

noncomputable instance : Union Class where
  union (x y : Class) := Classify fun z => z ∈ x ∨ z ∈ y
  
noncomputable instance : Inter Class where
  inter (x y : Class) := Classify fun z => z ∈ x ∧ z ∈ y
  
@[simp] theorem Union.dist : z ∈ x ∪ y ↔ (z ∈ x) ∨ (z ∈ y) := Iff.intro
  (fun h => (Class.classify.mp h).right)
  (fun h =>
    have h1 := Class.classify.mpr
    h.elim
      (fun zsx => h1 ⟨Ensemble.intro zsx, Or.inl zsx⟩)
      (fun zsy => h1 ⟨Ensemble.intro zsy, Or.inr zsy⟩)
  )

def Union.split : z ∈ x ∪ y → (z ∈ x) ∨ (z ∈ y) := Iff.mp Union.dist
def Union.intro : (z ∈ x) ∨ (z ∈ y) → z ∈ x ∪ y := Iff.mpr Union.dist

@[simp] theorem Inter.dist : z ∈ x ∩ y ↔ (z ∈ x) ∧ (z ∈ y) := Iff.intro
  (fun h => (Class.classify.mp h).right)
  (fun h => h.elim (fun zsx zsy => Class.classify.mpr ⟨Ensemble.intro zsx, ⟨zsx, zsy⟩⟩))

def Inter.split : z ∈ x ∩ y → (z ∈ x) ∧ (z ∈ y) := Iff.mp Inter.dist
def Inter.intro : (z ∈ x) ∧ (z ∈ y) → z ∈ x ∩ y := Iff.mpr Inter.dist

theorem Union.idem : y ∈ x ∪ x ↔ y ∈ x := by simp
theorem Union.idem_eq : x ∪ x = x := Class.eq fun _ => Union.idem

theorem Inter.idem : y ∈ x ∩ x ↔ y ∈ x := by simp
theorem Inter.idem_eq : x ∩ x = x := Class.eq fun _ => Inter.idem

@[symm, simp] theorem Union.comm : z ∈ x ∪ y → z ∈ y ∪ x := fun h => Union.intro (Union.split h).symm
theorem Union.comm_eq : x ∪ y = y ∪ x := Class.eq fun _ => Iff.intro Union.comm Union.comm

@[symm, simp] theorem Inter.comm : z ∈ x ∩ y → z ∈ y ∩ x := fun h => Inter.intro (Inter.split h).symm
theorem Inter.comm_eq : x ∩ y = y ∩ x := Class.eq fun _ => Iff.intro Inter.comm Inter.comm

private theorem Union.assoc_oneshot : w ∈ (x ∪ y) ∪ z → w ∈ x ∪ (y ∪ z) := fun h => Or.elim (Union.split h)
  (fun wsxy => Or.elim (Union.split wsxy) (fun wsx => Union.intro (Or.inl wsx)) (fun wsy => Union.intro (Or.inr (Union.intro (Or.inl wsy)))))
  (fun wsz => Union.intro (Or.inr (Union.intro (Or.inr wsz))))

private theorem Inter.assoc_oneshot : w ∈ (x ∩ y) ∩ z → w ∈ x ∩ (y ∩ z) := fun h =>
  have ⟨wsxy, wsz⟩ := Inter.split h; have ⟨wsx, wsy⟩ := Inter.split wsxy
  Inter.intro ⟨wsx, Inter.intro ⟨wsy, wsz⟩⟩

@[simp] theorem Union.assoc : w ∈ (x ∪ y) ∪ z ↔ w ∈ x ∪ (y ∪ z) := Iff.intro
  Union.assoc_oneshot
  fun h => Union.comm (Union.assoc_oneshot (Union.comm (Union.assoc_oneshot (Union.comm h))))
theorem Union.assoc_eq : (x ∪ y) ∪ z = x ∪ (y ∪ z) := Class.eq fun _ => Union.assoc

@[simp] theorem Inter.assoc : w ∈ (x ∩ y) ∩ z ↔ w ∈ x ∩ (y ∩ z) := Iff.intro
  Inter.assoc_oneshot
  fun h => Inter.comm (Inter.assoc_oneshot (Inter.comm (Inter.assoc_oneshot (Inter.comm h))))
theorem Inter.assoc_eq : (x ∩ y) ∩ z = x ∩ (y ∩ z) := Class.eq fun _ => Inter.assoc

@[simp] theorem Inter.dist_union : w ∈ x ∩ (y ∪ z) ↔ w ∈ (x ∩ y) ∪ (x ∩ z) := Iff.intro
  (fun h => have ⟨wsx, wsyoz⟩ := Inter.split h
    Union.intro
    ((Union.split wsyoz).elim (fun wsy => Or.inl (Inter.intro ⟨wsx, wsy⟩))
    (fun wsz => Or.inr (Inter.intro ⟨wsx, wsz⟩))))
  (fun h => Or.elim (Union.split h)
    (fun h => have ⟨wsx, wsy⟩ := Inter.split h; Inter.intro ⟨wsx, Union.intro (Or.inl wsy)⟩)
    (fun h => have ⟨wsx, wsz⟩ := Inter.split h; Inter.intro ⟨wsx, Union.intro (Or.inr wsz)⟩))
theorem Inter.dist_union_eq : x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z) := Class.eq fun _ => Inter.dist_union

def Inter.unfold_union : w ∈ x ∩ (y ∪ z) → w ∈ (x ∩ y) ∪ (x ∩ z) := Iff.mp Inter.dist_union
def Union.fold_inter : w ∈ (x ∩ y) ∪ (x ∩ z) → w ∈ x ∩ (y ∪ z) := Iff.mpr Inter.dist_union

@[simp] theorem Union.dist_inter : w ∈ x ∪ (y ∩ z) ↔ w ∈ (x ∪ y) ∩ (x ∪ z) := Iff.intro
  (fun h => Or.elim (Union.split h)
    (fun wsx => Inter.intro ⟨Union.intro (Or.inl wsx), Union.intro (Or.inl wsx)⟩)
    (fun h => have ⟨wsy, wsz⟩ := Inter.split h; Inter.intro ⟨Union.intro (Or.inr wsy), Union.intro (Or.inr wsz)⟩))
  (fun h => have ⟨h1, h2⟩ := Inter.split h
    match (Union.split h1), (Union.split h2) with
    | Or.inl wsx, _ | _, Or.inl wsx => Union.intro (Or.inl wsx)
    | Or.inr wsy, Or.inr wsz => Union.intro (Or.inr (Inter.intro ⟨wsy, wsz⟩)))
theorem Union.dist_inter_eq : x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z) := Class.eq fun _ => Union.dist_inter

def Union.unfold_inter : w ∈ x ∪ (y ∩ z) → w ∈ (x ∪ y) ∩ (x ∪ z) := Iff.mp Union.dist_inter
def Inter.fold_union : w ∈ (x ∪ y) ∩ (x ∪ z) → w ∈ x ∪ (y ∩ z):= Iff.mpr Union.dist_inter

noncomputable instance : Complement Class where
  complement x := Classify fun y => y ∉ x

@[simp] theorem Complement.compl_compl : y ∈ ~~~(~~~x) ↔ y ∈ x := Iff.intro
  (fun h =>
    have ⟨ensy, (h1 : y ∉ ~~~x)⟩ := Class.classify.mp h
    Classical.byContradiction fun fake : y ∉ x => h1 (Class.classify.mpr ⟨ensy, fake⟩))
  (fun h =>
    have h1 : y ∉ ~~~x := Classical.byContradiction fun fake : ¬¬ y ∈ ~~~x =>
      have fake : y ∈ ~~~x := Classical.not_not.mp fake
      have ⟨_, (h2 : y ∉ x)⟩ := Class.classify.mp fake
      h2 h;
    Classical.byContradiction fun fake : y ∉ ~~~(~~~x) =>
      have ensy : Ensemble y := ⟨x, h⟩
      fake (Class.classify.mpr ⟨ensy, h1⟩))
theorem Complement.compl_compl_eq : ~~~(~~~x) = x := Class.eq fun _ => Complement.compl_compl

def Complement.reduce : y ∈ ~~~(~~~x) → y ∈ x := Iff.mp Complement.compl_compl

@[simp] theorem Union.de_morgan : z ∈ ~~~(x ∪ y) ↔ z ∈ ~~~x ∩ ~~~y := Iff.intro
  (fun h =>
    have ⟨ensz, (h1 : z ∉ x ∪ y)⟩ := Class.classify.mp h
    have ⟨(znx : z ∉ x), (zny : z ∉ y)⟩ := not_or.mp (Not.imp h1 Union.intro)
    Inter.intro ⟨Class.classify.mpr ⟨ensz, znx⟩, Class.classify.mpr ⟨ensz, zny⟩⟩)
  (fun h =>
    have ⟨zcx, zcy⟩ := Inter.split h
    have ⟨ensz, znx⟩ := Class.classify.mp zcx
    have h1 := not_or.mpr ⟨znx, And.right (Class.classify.mp zcy)⟩
    have h2 : z ∉ x ∪ y := Not.intro fun fake => h1 (Union.split fake)
    Class.classify.mpr ⟨ensz, h2⟩)
theorem Union.de_morgan_eq : ~~~(x ∪ y) = ~~~x ∩ ~~~y := Class.eq fun _ => Union.de_morgan

@[simp] theorem Inter.de_morgan : z ∈ ~~~(x ∩ y) ↔ z ∈ ~~~x ∪ ~~~y := Iff.intro
  (fun h =>
    have ⟨ensz, (h1 : z ∉ x ∩ y)⟩ := Class.classify.mp h
    Union.intro (Or.imp 
      (fun h2 => Class.classify.mpr ⟨ensz, h2⟩)
      (fun h2 => Class.classify.mpr ⟨ensz, h2⟩)
      (Classical.not_and_iff_not_or_not.mp (Not.imp h1 Inter.intro))
    ))
  (fun h =>
    have h1 := Or.imp
      (fun c => Class.classify.mp c)
      (fun c => Class.classify.mp c)
      (Union.split h)
    have h2 : z ∉ x ∩ y := Classical.byContradiction fun fake =>
      have ⟨zsx, zsy⟩ := Inter.split (Classical.not_not.mp fake)
      match h1 with
      | Or.inl ⟨_, znx⟩ => znx zsx
      | Or.inr ⟨_, zny⟩ => zny zsy
    Class.classify.mpr ⟨⟨(~~~x ∪ ~~~y), h⟩, h2⟩)
theorem Inter.de_morgan_eq : ~~~(x ∩ y) = ~~~x ∪ ~~~y := Class.eq fun _ => Inter.de_morgan

noncomputable instance : Sub Class where
  sub (x y) := x ∩ ~~~y

theorem Sub.intro : z ∈ x → z ∉ y → z ∈ x - y := fun h1 h2 =>
  Inter.intro ⟨h1, Class.classify.mpr ⟨⟨x, h1⟩, h2⟩⟩

theorem Sub.split : z ∈ x - y → z ∈ x ∧ z ∉ y := fun h =>
  And.imp_right (fun h1 => And.right (Class.classify.mp h1)) (Inter.split h)

@[simp] theorem Sub.iff_and : z ∈ x - y ↔ z ∈ x ∧ z ∉ y :=
  Iff.intro Sub.split fun h => Sub.intro h.left h.right

@[simp,symm] theorem Sub.inter_assoc : w ∈ x ∩ (y - z) ↔ w ∈ (x ∩ y) - z := Inter.assoc.symm
theorem Sub.inter_assoc_eq : x ∩ (y - z) = (x ∩ y) - z := Class.eq fun _ => Sub.inter_assoc

theorem Sub.elim_union : z ∈ x ∪ y - x → z ∈ y := fun h => have ⟨h1, h2⟩ := Sub.split h; (Union.split h1).resolve_left h2
theorem Sub.elim_union' : z ∈ x ∪ y - y → z ∈ x := fun h => have ⟨h1, h2⟩ := Sub.split h; (Union.split h1).resolve_right h2

noncomputable instance : EmptyCollection Class where
  emptyCollection := Classify fun x => x ≠ x

noncomputable abbrev Φ : Class := ∅

theorem Class.not_in_empty : x ∉ Φ := Not.intro fun fake => (Class.classify.mp fake).right rfl

theorem Sub.elim_empty : y ∈ x - Φ ↔ y ∈ x := Iff.intro
  (fun h => have ⟨h1, _⟩ := Sub.split h; h1)
  (fun h => Sub.intro h Class.not_in_empty)
@[simp] theorem Sub.elim_empty_eq : x - Φ = x := Class.eq fun _ => Sub.elim_empty

@[simp] theorem Union.elim_empty : y ∈ Φ ∪ x ↔ y ∈ x := Iff.intro
  (fun h => Or.resolve_left (Union.split h) Class.not_in_empty)
  (fun h => Union.intro (Or.inr h))
theorem Union.elim_empty_eq : Φ ∪ x = x := Class.eq fun _ => Union.elim_empty

@[simp] theorem Inter.elim_empty : y ∈ Φ ∩ x ↔ y ∈ Φ := Iff.intro
  (fun h => And.left (Inter.split h))
  (fun h => Class.not_in_empty.elim h)
theorem Inter.elim_empty_eq : Φ ∩ x = Φ := Class.eq fun _ => Inter.elim_empty

noncomputable def μ := Classify fun x => x = x

theorem Class.in_complete : x ∈ μ ↔ Ensemble x := Iff.intro
  (fun h => And.left (Class.classify.mp h))
  (fun h => Class.classify.mpr ⟨h, rfl⟩)

@[simp] theorem Union.elim_complete : y ∈ x ∪ μ ↔ y ∈ μ := Iff.intro
  (fun h => Class.in_complete.mpr ⟨x ∪ μ, h⟩)
  (fun h => Union.intro (Or.inr h))
theorem Union.elim_complete_eq : x ∪ μ = μ := Class.eq fun _ => Union.elim_complete

@[simp] theorem Inter.elim_complete : y ∈ x ∩ μ ↔ y ∈ x := Iff.intro
  (fun h => And.left (Inter.split h))
  (fun h => Inter.intro ⟨h, Class.in_complete.mpr ⟨x, h⟩⟩)
theorem Inter.elim_complete_eq : x ∩ μ = x := Class.eq fun _ => Inter.elim_complete

theorem complete_compl_empty : x ∈ μ ↔ x ∈ ~~~Φ := Iff.intro
  (fun h => Class.classify.mpr ⟨⟨μ, h⟩, Class.not_in_empty⟩)
  (fun h => Class.in_complete.mpr ⟨~~~Φ, h⟩)
theorem complete_compl_empty_eq : μ = ~~~Φ := Class.eq fun _ => complete_compl_empty

theorem empty_compl_complete : x ∈ Φ ↔ x ∈ ~~~μ := Iff.intro
  (fun h => Class.not_in_empty.elim h)
  (fun h => have ⟨ensx, not⟩ := Class.classify.mp h; not.elim (Class.in_complete.mpr ensx))
theorem empty_compl_complete_eq : Φ = ~~~μ := Class.eq fun _ => empty_compl_complete

noncomputable def SInter (x : Class) := Classify fun z => ∀ y, y ∈ x → z ∈ y
noncomputable def SUnion (x : Class) := Classify fun z => ∃ y, z ∈ y ∧ y ∈ x

prefix:85 "∩" => SInter
prefix:85 "∪" => SUnion

@[simp] theorem sinter_empty_is_complete : x ∈ ∩Φ ↔ x ∈ μ := Iff.intro
  (fun h => Class.in_complete.mpr ⟨∩Φ, h⟩)
  (fun h => Class.classify.mpr ⟨⟨μ, h⟩, fun _ fake => Class.not_in_empty.elim fake⟩)
theorem sinter_empty_is_complete_eq : ∩Φ = μ := Class.eq fun _ => sinter_empty_is_complete

@[simp] theorem sunion_empty_is_empty : x ∈ ∪Φ ↔ x ∈ Φ := Iff.intro
  (fun h => have ⟨_, ⟨_, h1⟩⟩ := Class.classify.mp h; Not.elim Class.not_in_empty h1.right)
  (fun h => Class.not_in_empty.elim h)
theorem sunion_empty_is_empty_eq : ∪Φ = Φ := Class.eq fun _ => sunion_empty_is_empty

instance : HasSubset Class where
  Subset x y := ∀ z, z ∈ x → z ∈ y

@[simp] theorem empty_is_subset : Φ ⊆ x := fun _ h => Class.not_in_empty.elim h
@[simp] theorem complete_is_superset : x ⊆ μ := fun _ h => Class.in_complete.mpr ⟨x, h⟩
@[refl, simp] theorem subset_rfl : x ⊆ x := fun _ => id 

@[simp, symm] theorem subset_antisymm : x ⊆ y ∧ y ⊆ x ↔ x = y := Iff.intro
  (fun ⟨h1, h2⟩ => Class.eq fun z => Iff.intro (fun zsx => h1 z zsx) (fun zsy => h2 z zsy))
  (fun h => by rw[h]; simp)

@[simp] theorem subset_with_union : x ⊆ y → x ⊆ y ∪ z := fun h w wsx => Union.intro (Or.inl (h w wsx))
theorem subset_of_union : x ⊆ x ∪ y := by simp
theorem subset_of_union' : y ⊆ x ∪ y := by rw[Union.comm_eq]; simp
@[simp] theorem inter_is_subset : x ∩ y ⊆ x := fun _ h => And.left (Inter.split h)

@[simp] theorem subset_trans : x ⊆ y → y ⊆ z → x ⊆ z := fun h1 h2 w zsx => h2 w (h1 w zsx)

@[simp] theorem union_absorb_subset : x ∪ y = y ↔ x ⊆ y := Iff.intro
  (fun h => by rw[← h]; simp)
  (fun h => Class.eq fun z => Iff.intro
    (fun zsxy => (Union.split zsxy).elim (fun zsx => h z zsx) id)
    (fun zsy => Union.intro (Or.inr zsy)))
@[simp] theorem inter_absorb_subset : x ∩ y = x ↔ x ⊆ y := Iff.intro
  (fun h => by rw[← h]; rw[Inter.comm_eq]; simp)
  (fun h => Class.eq fun z => Iff.intro
    (fun zsxy => And.left (Inter.split zsxy))
    (fun zsx => Inter.intro ⟨zsx, h z zsx⟩))

theorem sunion_monotone : x ⊆ y → ∪x ⊆ ∪y := fun h _ zsux =>
  have ⟨ensz, ⟨w, ⟨zsw, wsx⟩⟩⟩ := Class.classify.mp zsux
  Class.classify.mpr ⟨ensz, ⟨w, ⟨zsw, h w wsx⟩⟩⟩
theorem sinter_monotone : x ⊆ y → ∩y ⊆ ∩x := fun h _ zsiy =>
  have ⟨ensz, h1⟩ := Class.classify.mp zsiy
  Class.classify.mpr ⟨ensz, fun w wsx => have wsy := h w wsx; h1 w wsy⟩

theorem sunion_monotone_mem : x ∈ y → x ⊆ ∪y := fun xsy _ zsx  =>
  Class.classify.mpr ⟨⟨x, zsx⟩, ⟨x, ⟨zsx, xsy⟩⟩⟩
theorem sinter_monotone_mem : x ∈ y → ∩y ⊆ x := fun xsy _ zsiy =>
  And.right (Class.classify.mp zsiy) x xsy

axiom Class.subsets : ∀ {x}, Ensemble x → ∃ y, Ensemble y ∧ (∀ z, z ⊆ x -> z ∈ y)

theorem Ensemble.recursive : Ensemble x → ∃ y, Ensemble y ∧ x ∈ y := fun h =>
  have ⟨y, ⟨ensy, h1⟩⟩ := (Class.subsets h)
  ⟨y, ⟨ensy, h1 x subset_rfl⟩⟩

theorem Ensemble.mp : Ensemble x → y ⊆ x → Ensemble y := fun ensx h =>
  have ⟨z, ⟨_, h1⟩⟩ := Class.subsets ensx
  ⟨z, h1 y h⟩

@[simp] theorem sinter_complete_is_empty : x ∈ ∩μ ↔ x ∈ Φ := Iff.intro
  (fun h =>
    have ⟨ensx, h1⟩ := Class.classify.mp h
    have h2 := Ensemble.mp ensx empty_is_subset
    h1 Φ (Class.in_complete.mpr h2))
  (fun h =>(Class.not_in_empty h).elim)
theorem sinter_complete_is_empty_eq : ∩μ = Φ := Class.eq fun _ => sinter_complete_is_empty

@[simp] theorem sunion_complete_is_complete : x ∈ ∪μ ↔ x ∈ μ := Iff.intro
  (fun h =>
    have ⟨_, ⟨y, xsy, _⟩⟩ := Class.classify.mp h
    Class.in_complete.mpr ⟨y, xsy⟩)
  (fun h =>
    have ensx := Class.in_complete.mp h
    have ⟨y, ⟨ensy, xsy⟩⟩ := Ensemble.recursive ensx
    Class.classify.mpr ⟨ensx, ⟨y, ⟨xsy, Class.in_complete.mpr ensy⟩⟩⟩)
theorem sunion_complete_is_complete_eq : ∪μ = μ := Class.eq fun _ => sunion_complete_is_complete

theorem Class.sib_exist_non_empty : x ≠ Φ ↔ ∃ y, y ∈ x := Iff.intro
  (fun h => Classical.byContradiction fun fake =>
    h (Class.eq fun z => Iff.intro
      (fun h1 => (not_exists.mp fake z h1).elim)
      (fun h1 => (Class.not_in_empty h1).elim)) )
  (fun ⟨y, ysx⟩ => Not.intro fun fake =>
    have fake1 : y ∈ Φ := by rw[fake] at ysx; exact ysx
    Class.not_in_empty fake1)

theorem sinter_ens_non_empty : x ≠ Φ → Ensemble (∩x) := fun h =>
  have ⟨_, ysx⟩ := Class.sib_exist_non_empty.mp h
  Ensemble.mp (Ensemble.intro ysx) (sinter_monotone_mem ysx)

noncomputable def Power (x : Class) := Classify fun y => y ⊆ x
noncomputable abbrev pow := Power

@[simp] theorem complete_power_rfl : x ∈ μ ↔ x ∈ pow μ := Iff.intro
  (fun h => Class.classify.mpr ⟨Class.in_complete.mp h, complete_is_superset⟩)
  (fun h => have ⟨ensx, _⟩ := Class.classify.mp h; Class.in_complete.mpr ensx)
theorem complete_power_rfl_eq : μ = pow μ := Class.eq fun _ => complete_power_rfl

@[simp] theorem Ensemble.map_pow : Ensemble x → Ensemble (pow x) := fun ensx =>
  have ⟨_, ⟨ensy, h⟩⟩ := Class.subsets ensx
  Ensemble.mp ensy fun z zpx => have ⟨_, zssx⟩ := Class.classify.mp zpx; h z zssx

theorem Class.subsets_pow : Ensemble x → ∀ y, y ⊆ x ↔ y ∈ pow x := fun ensx _ => Iff.intro
  (fun h => Class.classify.mpr ⟨Ensemble.mp ensx h, h⟩)
  (fun h => have ans := And.right (Class.classify.mp h); ans)

theorem Class.in_pow : Ensemble x → x ∈ pow x := fun h =>
  Class.classify.mpr ⟨h, subset_rfl⟩

noncomputable def Nens := Classify fun x => x ∉ x

theorem Nens.nens : ¬Ensemble Nens := fun ensn => Classical.byCases
  (fun h : Nens ∈ Nens => have ⟨_, h1⟩ := Class.classify.mp h; h1 h)
  (fun h : Nens ∉ Nens => h (Class.classify.mpr ⟨ensn, h⟩))

theorem complete_nens : ¬Ensemble μ := fun ensm =>
  Nens.nens (Ensemble.mp ensm complete_is_superset)

noncomputable instance : Singleton Class Class where
  singleton x := Classify fun y => x ∈ μ → y = x

noncomputable abbrev singleton (x : Class) : Class := {x}

theorem singleton_eq : Ensemble y → x ∈ ({y} : Class) → x = y := fun ensy h =>
  have ⟨_, h1⟩ := Class.classify.mp h
  h1 (Class.in_complete.mpr ensy)

@[simp] theorem Class.in_singleton : Ensemble x → x ∈ singleton x := fun ensx =>
  Class.classify.mpr ⟨ensx, fun _ => rfl⟩

theorem singleton_mp : x ∈ singleton y → y = z → x ∈ singleton z := fun h eq =>
  by rw[← eq]; exact h

theorem singleton_mpr : Ensemble x → y ∈ singleton x ∧ z ∈ singleton x → y = z := fun ensx ⟨h1, h2⟩ =>
  have ⟨ensy, h1⟩ := Class.classify.mp h1
  have ⟨ensz, h2⟩ := Class.classify.mp h2
  by simp[h1, h2, Class.in_complete.mpr ensx]
theorem singleton_smpr : Ensemble x → y ∈ singleton x → x = y := fun ensx h =>
  singleton_mpr ensx ⟨Class.in_singleton ensx, h⟩

@[simp] theorem singleton_subset_pow : Ensemble x → {x} ⊆ pow x := fun ensx y h =>
  have h1 := singleton_smpr ensx h
  by simp[h1]; rw[← h1]; exact Class.in_pow ensx

theorem Ensemble.map_singleton : Ensemble x → Ensemble {x} := fun ensx =>
  Ensemble.mp (Ensemble.map_pow ensx) (singleton_subset_pow ensx)

@[simp] theorem nens_singleton_is_complete : {x} = μ ↔ ¬Ensemble x := Iff.intro
  (fun h => complete_nens.imp fun ensx =>
    have h1 := Ensemble.map_singleton ensx
    by rw[h] at h1; exact h1)
  (fun h => Class.eq fun y => Iff.intro
    (fun h1 => complete_is_superset y h1)
    (fun h1 => have ensy := Class.in_complete.mp h1
      Class.classify.mpr ⟨ensy, fun fake => h.elim (Class.in_complete.mp fake)⟩))

theorem Ensemble.unwrap_singleton : Ensemble {x} → Ensemble x := fun h => Classical.byContradiction fun fake =>
  have eq := nens_singleton_is_complete.mpr fake
  by rw[eq] at h; exact complete_nens h 

@[simp] theorem Ensemble.iff_singleton : Ensemble x ↔ Ensemble {x} := Iff.intro Ensemble.map_singleton Ensemble.unwrap_singleton

theorem sinter_singleton_rfl : Ensemble x → ∩{x} = x := fun h => Class.eq fun y => Iff.intro
  (fun h1 =>
    have ⟨ensy, h2⟩ := Class.classify.mp h1
    h2 x (Class.in_singleton h))
  (fun h1 => Class.classify.mpr ⟨⟨x, h1⟩, fun z h2 =>
    have ⟨ensz, h3⟩ := Class.classify.mp h2
    have h3 := h3 (Class.in_complete.mpr h)
    by rw[← h3] at h1; exact h1⟩)

theorem sunion_singleton_rfl : Ensemble x → ∪{x} = x := fun h => Class.eq fun y => Iff.intro
  (fun h1 =>
    have ⟨ensy, ⟨z, ⟨h2, h3⟩⟩⟩ := Class.classify.mp h1
    have h4 := singleton_smpr h h3
    by rw[← h4] at h2; exact h2)
  (fun h1 => Class.classify.mpr ⟨⟨x, h1⟩, ⟨x, ⟨h1, Class.in_singleton h⟩⟩⟩)

theorem nens_sinter_singleton : ¬Ensemble x → ∩{x} = Φ := fun h =>
  have h1 := nens_singleton_is_complete.mpr h
  by rw[h1]; apply sinter_complete_is_empty_eq

theorem nens_sunion_singleton : ¬Ensemble x → ∪{x} = μ := fun h =>
  have h1 := nens_singleton_is_complete.mpr h
  by rw[h1]; apply sunion_complete_is_complete_eq

@[simp] axiom Ensemble.map_union : Ensemble x → Ensemble y → Ensemble (x ∪ y)

@[simp] theorem Ensemble.unwrap_union : Ensemble (x ∪ y) → Ensemble x ∧ Ensemble y := fun h =>
  ⟨Ensemble.mp h subset_of_union, Ensemble.mp h subset_of_union'⟩

-- unordered
noncomputable instance : Insert Class Class where
  insert x y := {x} ∪ y

noncomputable abbrev Unordered (x y : Class) : Class := {x, y}

theorem Ensemble.map_unordered : Ensemble x → Ensemble y → Ensemble {x, y} := fun h1 h2 =>
  Ensemble.map_union (Ensemble.map_singleton h1) (Ensemble.map_singleton h2)
theorem Ensemble.unwrap_unordered : Ensemble {x, y} → Ensemble x ∧ Ensemble y := fun h =>
  (Ensemble.unwrap_union h).imp Ensemble.unwrap_singleton Ensemble.unwrap_singleton

@[simp] theorem Ensemble.map_unordered_iff : Ensemble x ∧ Ensemble y ↔ Ensemble {x, y} := Iff.intro
  (fun ⟨a, b⟩ => Ensemble.map_unordered a b)
  Ensemble.unwrap_unordered

theorem pick_from_unordered : Ensemble x → Ensemble y → (∀ z, z ∈ ({x, y} : Class) ↔ z = x ∨ z = y) := fun ensx ensy z => Iff.intro
  (fun zsxy => have ⟨ensz, or⟩ := Class.classify.mp zsxy
    have intermediary := or.imp (singleton_smpr ensx) (singleton_smpr ensy)
    intermediary.imp Eq.symm Eq.symm)
  (fun h => h.elim
    (fun h => by rw[h]; exact Union.intro (Or.inl (Class.in_singleton ensx)))
    (fun h => by rw[h]; exact Union.intro (Or.inr (Class.in_singleton ensy))))

@[simp] theorem in_unordered : Ensemble x → x ∈ ({x, y} : Class) := fun ensx =>
  Union.intro (Or.inl (Class.in_singleton ensx))
@[simp] theorem in_unordered' : Ensemble y → y ∈ ({x, y} : Class) := fun ensy =>
  Union.intro (Or.inr (Class.in_singleton ensy))

theorem nens_unordered_complete : ¬Ensemble x ∨ ¬Ensemble y ↔ {x, y} = μ := Iff.intro
  (fun h =>
    have h1 := h.imp nens_singleton_is_complete.mpr nens_singleton_is_complete.mpr
    h1.elim
      (fun h2 => by show ({x} ∪ {y} = μ); rw[h2]; rw[Union.comm_eq]; apply Union.elim_complete_eq)
      (fun h2 => by show ({x} ∪ {y} = μ); rw[h2]; apply Union.elim_complete_eq))
  (fun h =>
    have h1 : ¬Ensemble {x, y} := by have h1 := complete_nens; rw[← h] at h1; exact h1
    Classical.not_and_iff_not_or_not.mp (h1.imp Ensemble.map_unordered_iff.mp))

@[simp] theorem sinter_unordered_is_inter : Ensemble x ∧ Ensemble y → ∩{x, y} = x ∩ y := fun ⟨ensx, ensy⟩ => Class.eq fun z => Iff.intro
  (fun h => have ⟨ensz, h1⟩ := Class.classify.mp h; Inter.intro ⟨h1 x (in_unordered ensx), h1 y (in_unordered' ensy)⟩)
  (fun h =>
    have ⟨h1, h2⟩ := Inter.split h
    Class.classify.mpr ⟨Ensemble.intro h, fun w h =>
      have h3 := (pick_from_unordered ensx ensy w).mp h
      h3.elim (fun h => by rw[h]; exact h1) (fun h => by rw[h]; exact h2)⟩)

@[simp] theorem sunion_unordered_is_union : Ensemble x ∧ Ensemble y → ∪{x, y} = x ∪ y := fun ⟨ensx, ensy⟩ => Class.eq fun z => Iff.intro
  (fun h =>
    have ⟨ensz, ⟨w, ⟨h1, h2⟩⟩⟩ := Class.classify.mp h
    have h3 := (pick_from_unordered ensx ensy w).mp h2
    Union.intro (h3.imp (fun h => by rw[← h]; exact h1) (fun h => by rw[← h]; exact h1)))
  (fun h =>
    have h1 := Union.split h
    Class.classify.mpr (And.intro (Ensemble.intro h)
    (h1.elim
      (fun h => ⟨x, ⟨h, in_unordered  ensx⟩⟩)
      (fun h => ⟨y, ⟨h, in_unordered' ensy⟩⟩))))

noncomputable def Ordered (x y : Class) : Class := {{x}, {x, y}}

macro_rules
| `(($a , $b)) => `(Ordered $a $b)

theorem Ensemble.map_ordered : Ensemble x → Ensemble y → Ensemble (x, y) := fun ensx ensy =>
  Ensemble.map_unordered (Ensemble.map_singleton ensx) (Ensemble.map_unordered ensx ensy)

theorem Ensemble.unwrap_ordered : Ensemble (x, y) → Ensemble x ∧ Ensemble y := fun h => And.imp
  Ensemble.unwrap_singleton
  (fun h => And.right (Ensemble.unwrap_unordered h))
  (Ensemble.unwrap_unordered h)

theorem Ensemble.unwrap_ordered_l : Ensemble (x, y) → Ensemble x := fun h => And.left (Ensemble.unwrap_ordered h)
theorem Ensemble.unwrap_ordered_r : Ensemble (x, y) → Ensemble y := fun h => And.right (Ensemble.unwrap_ordered h)

@[simp] theorem Ensemble.map_ordered_iff : Ensemble x ∧ Ensemble y ↔ Ensemble (x, y) := Iff.intro
  (fun ⟨h1, h2⟩ => Ensemble.map_ordered h1 h2) Ensemble.unwrap_ordered

theorem nens_ordered_complete : ¬Ensemble x ∨ ¬Ensemble y ↔ (x, y) = μ := Iff.intro
  (fun h => by
      have h1 := nens_unordered_complete.mp h
      show {{x}, {x, y}} = μ; rw[h1]
      exact nens_unordered_complete.mp (Or.inr complete_nens))
  (fun h => Or.elim (nens_unordered_complete.mpr h)
    (fun h => Or.inl (h.imp Ensemble.map_singleton))
    (fun h => Classical.not_and_iff_not_or_not.mp (h.imp Ensemble.map_unordered_iff.mp)))

@[simp] theorem sunion_ordered_is_unordered : Ensemble x ∧ Ensemble y → ∪(x, y) = {x, y} := fun ⟨ensx, ensy⟩ => Class.eq fun z =>
  have h1 := sunion_unordered_is_union ⟨Ensemble.map_singleton ensx, Ensemble.map_unordered ensx ensy⟩
  Iff.intro
    (fun h =>
      have h2 := Union.split ((Class.eq_iff.mp h1 z).mp h)
      h2.elim (fun h => Union.intro (Or.inl h)) id)
    (fun h => by
      show z ∈ ∪{{x}, {x, y}}; rw[h1]
      exact Union.intro (Or.inr h))

@[simp] theorem sinter_ordered_is_singleton : Ensemble x ∧ Ensemble y → ∩(x, y) = {x} := fun ⟨ensx, ensy⟩ => Class.eq fun z =>
  have h1 := sinter_unordered_is_inter ⟨Ensemble.map_singleton ensx, Ensemble.map_unordered ensx ensy⟩
  by
    show z ∈ ∩{{x}, {x, y}} ↔ z ∈ {x}; rw[h1];
    exact Iff.intro
      (fun h => And.left (Inter.split h))
      (fun h => Inter.intro ⟨h, Union.intro (Or.inl h)⟩)

-- unwraps an Ordered
noncomputable def First x := ∩∩x
noncomputable def Second x := (∩∪x) ∪ (∪∪x - ∪∩x)

theorem second_complete_is_complete : Second μ = μ := by
  show ∩∪μ ∪ (∪∪μ - ∪∩μ) = μ
  rw[sunion_complete_is_complete_eq, sinter_complete_is_empty_eq, sunion_empty_is_empty_eq, sunion_complete_is_complete_eq]
  rw[Union.elim_empty_eq]; exact Sub.elim_empty_eq

@[simp] theorem unwrap_ordered_first : Ensemble x ∧ Ensemble y → First (x, y) = x := fun h => by
  show ∩∩(x, y) = x
  rw[sinter_ordered_is_singleton h, sinter_singleton_rfl]
  exact h.left

@[simp] theorem unwrap_ordered_second : Ensemble x ∧ Ensemble y → Second (x, y) = y := fun h => by
  show ∩∪(x, y) ∪ (∪∪(x, y) - ∪∩(x, y)) = y
  rw[sunion_ordered_is_unordered h, sinter_ordered_is_singleton h, sinter_unordered_is_inter h, sunion_unordered_is_union h]
  rw[sunion_singleton_rfl h.left]
  exact Class.eq fun z => Iff.intro
    (fun h => (Union.split h).elim (fun h => And.right (Inter.split h)) Sub.elim_union)
    (fun h => Union.intro (Classical.byCases
      (fun h1 : z ∈ x => Or.inl (Inter.intro ⟨h1, h⟩))
      (fun h1 : z ∉ x => Or.inr (Sub.intro (Union.intro (Or.inr h)) h1))))

theorem nens_ordered_components_complete : ¬Ensemble x ∨ ¬Ensemble y → First (x, y) = μ ∧ Second (x, y) = μ := fun h => by
  show ∩∩(x, y) = μ ∧ (∩∪(x, y)) ∪ (∪∪(x, y) - ∪∩(x, y)) = μ
  rw[nens_ordered_complete.mp h]
  rw[sinter_complete_is_empty_eq, sunion_complete_is_complete_eq, sinter_empty_is_complete_eq]
  rw[sinter_complete_is_empty_eq, sunion_complete_is_complete_eq, sunion_empty_is_empty_eq]
  rw[Sub.elim_empty_eq, Union.elim_empty_eq]
  constructor
  · rfl
  · rfl

theorem ordered_rfl : Ensemble x ∧ Ensemble y → ((x, y) = (u, v) ↔ x = u ∧ y = v) := fun ens => Iff.intro
  (fun h =>
    have snd := unwrap_ordered_second ens
    have ens' := Ensemble.unwrap_ordered (by have enso := Ensemble.map_ordered ens.left ens.right; rw[h] at enso; exact enso)
    have hx : x = u := by
      have fst := unwrap_ordered_first ens;
      have fst' := unwrap_ordered_first ens'
      rw[h] at fst; exact Eq.trans fst.symm fst'
    have hy : y = v := by
      have snd := unwrap_ordered_second ens;
      have snd' := unwrap_ordered_second ens'
      rw[h] at snd; exact Eq.trans snd.symm snd'
    ⟨hx, hy⟩)
  fun ⟨h1, h2⟩ => by rw[h1, h2]

theorem pins {a b c d : Class} : Ensemble c ∧ Ensemble d → (a, b) ∈ ({(c, d)} : Class) → a = c ∧ b = d := fun ⟨ensc, ensd⟩ h =>
  have eq := singleton_eq (Ensemble.map_ordered ensc ensd) h
  have h1 := (ordered_rfl ⟨ensc, ensd⟩).mp eq.symm
  h1.imp Eq.symm Eq.symm

def Relation (r : Class) := ∀ z, z ∈ r → ∃ x y, z = (x, y)

noncomputable abbrev PairedClassify : (Class → Class → Prop) → Class := fun p =>
  Classify fun z => ∃ x y, z = (x, y) ∧ p x y

theorem PairedClassify.relative {P : Class → Class → Prop} : Relation (PairedClassify P) := fun _ h =>
  have ⟨_, ⟨x, ⟨y, ⟨h1, _⟩⟩⟩⟩ := Class.classify.mp h; ⟨x, ⟨y, h1⟩⟩

theorem Relation.map_union : Relation x → Relation y → Relation (x ∪ y) := fun rx ry z h =>
  (Union.split h).elim (fun h => rx z h) (fun h => ry z h)

@[simp] theorem Class.paired_classify {P : Class → Class → Prop} : (x, y) ∈ PairedClassify P ↔ Ensemble (x, y) ∧ P x y := Iff.intro
  (fun h =>
    have ⟨ens, ⟨a, ⟨b, ⟨h1, h2⟩⟩⟩⟩ := Class.classify.mp h
    have ⟨xsa, ysb⟩ := (ordered_rfl (Ensemble.unwrap_ordered ens)).mp h1
    ⟨ens, by rw[← xsa, ← ysb] at h2; exact h2⟩)
  (fun ⟨ens, h⟩ => Class.classify.mpr ⟨ens, ⟨x, ⟨y, ⟨by rfl, h⟩⟩⟩⟩)

theorem Class.paired_eq {a b : Class} : Relation a → Relation b → (∀ x y, (x, y) ∈ a ↔ (x, y) ∈ b) → a = b :=
  fun ra rb h => Class.eq fun z => Iff.intro
    (fun h1 => by have ⟨x, ⟨y, h2⟩⟩ := ra z h1; rw[h2]; rw[h2] at h1; exact (h x y).mp h1)
    (fun h1 => by have ⟨x, ⟨y, h2⟩⟩ := rb z h1; rw[h2]; rw[h2] at h1; exact (h x y).mpr h1)

noncomputable def Composition (r s : Class) := PairedClassify fun x z => ∃ y, (x, y) ∈ s ∧ (y, z) ∈ r

infixr:90 " ∘ "  => Composition

variable {a b f r s t : Class}

theorem Composition.assoc : (x, y) ∈ (r ∘ s) ∘ t → (x, y) ∈ r ∘ (s ∘ t) := fun h =>
  have ⟨ensxy, ⟨z, ⟨h1, h'⟩⟩⟩ := Class.paired_classify.mp h
  have ⟨_, ⟨w, ⟨h2, h3⟩⟩⟩ := Class.paired_classify.mp h'
  have ensw := Ensemble.unwrap_ordered_r (Ensemble.intro h2)
  have h4 : (x, w) ∈ s ∘ t := Class.paired_classify.mpr ⟨Ensemble.map_ordered (Ensemble.unwrap_ordered_l ensxy) ensw, ⟨z, ⟨h1, h2⟩⟩⟩
  Class.paired_classify.mpr ⟨ensxy, ⟨w, ⟨h4, h3⟩⟩⟩

theorem Composition.assoc' : (x, y) ∈ r ∘ (s ∘ t) → (x, y) ∈ (r ∘ s) ∘ t := fun h =>
  have ⟨ensxy, ⟨z, ⟨h', h1⟩⟩⟩ := Class.paired_classify.mp h
  have ⟨_, ⟨w, ⟨h2, h3⟩⟩⟩ := Class.paired_classify.mp h'
  have ensw := Ensemble.unwrap_ordered_r (Ensemble.intro h2)
  have h4 : (w, y) ∈ r ∘ s := Class.paired_classify.mpr ⟨Ensemble.map_ordered ensw (Ensemble.unwrap_ordered_r ensxy), ⟨z, ⟨h3, h1⟩⟩⟩
  Class.paired_classify.mpr ⟨ensxy, ⟨w, ⟨h2, h4⟩⟩⟩

theorem Composition.assoc_eq : (r ∘ s) ∘ t = r ∘ (s ∘ t) :=
  Class.paired_eq PairedClassify.relative PairedClassify.relative fun _ _ => Iff.intro Composition.assoc Composition.assoc'

theorem Composition.split_union : (x, y) ∈ r ∘ (s ∪ t) → (x, y) ∈ (r ∘ s) ∪ (r ∘ t) := fun h =>
  have ⟨ensxy, ⟨z, ⟨h1, h2⟩⟩⟩ := Class.paired_classify.mp h
  Union.intro ((Union.split h1).imp
    (fun h => Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨h, h2⟩⟩⟩)
    (fun h => Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨h, h2⟩⟩⟩))

theorem Composition.merge_union : (x, y) ∈ (r ∘ s) ∪ (r ∘ t) → (x, y) ∈ r ∘ (s ∪ t) := fun h => (Union.split h).elim
  (fun h =>
    have ⟨ensxy, ⟨z, ⟨h1, h2⟩⟩⟩ := Class.paired_classify.mp h
    Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨Union.intro (Or.inl h1), h2⟩⟩⟩)
  (fun h =>
    have ⟨ensxy, ⟨z, ⟨h1, h2⟩⟩⟩ := Class.paired_classify.mp h
    Class.paired_classify.mpr ⟨ensxy, ⟨z, ⟨Union.intro (Or.inr h1), h2⟩⟩⟩)

theorem Composition.dist_union_eq : r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t) := Class.paired_eq
  PairedClassify.relative (Relation.map_union PairedClassify.relative PairedClassify.relative)
  fun _ _ => Iff.intro Composition.split_union Composition.merge_union
