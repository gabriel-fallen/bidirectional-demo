def hello := "world"

@[reducible] def Name := Nat

inductive SType
  | tbool
  | tfun : SType -> SType -> SType
  deriving Repr

def SType.beq : SType -> SType -> Bool
  | tbool, tbool => true
  | tfun τ1 τ2, tfun σ1 σ2 => (beq τ1 σ1) && (beq τ1 σ2)
  | _, _ => false

instance : BEq SType where
  beq := SType.beq

def SType.toString : SType -> String
  | tbool => "Bool"
  | tfun τ1 τ2 => "(" ++ toString τ1 ++ " --> " ++ toString τ2 ++ ")"

instance : ToString SType where
  toString := SType.toString

inductive STerm
  | var : Name -> STerm
  | app : STerm -> STerm -> STerm
  | abs : Name -> STerm -> STerm
  | strue
  | sfalse
  | ite : STerm -> STerm -> STerm -> STerm
  | ann : STerm -> SType -> STerm
  deriving Repr

def STerm.toString : STerm -> String
  | var n => ToString.toString n
  | app t1 t2 => "(" ++ toString t1 ++ " " ++ toString t2 ++ ")"
  | abs n t => "(λ " ++ ToString.toString n ++ ". " ++ toString t ++ ")"
  | strue  => "true"
  | sfalse => "false"
  | ite c t e => "if " ++ toString c ++ " then " ++ toString t ++ " else " ++ toString e
  | ann t τ => toString t ++ " : " ++ τ.toString

instance : ToString STerm where
  toString := STerm.toString

def Ctx := List (Name × SType)
@[reducible] def Result α := Sum String α

def Option.elim (o : Option α) (err : Unit -> β) (f : α -> β) : β := match o with
  | none   => err ()
  | some v => f v

def all_right (r1 : Result Unit) (r2 : Result Unit) (r3 : Result Unit) : Result Unit :=
  match r1 with
  | Sum.inl _ => r1
  | _ => match r2 with
         | Sum.inl _ => r2
         | _ => r3

def wrong_type (t : STerm) (τ : SType) : String :=
  "Type mismatch: the term '" ++ toString t ++ "' doesn't check against '" ++ toString τ ++ "'"

def expected_function (t : STerm) (τ : SType) : String :=
  "The term '" ++ t.toString ++ "' is expected to have a function type while having type '" ++ τ.toString ++ "'"

mutual
  open Sum
  open STerm
  open SType

  partial def check (Γ : Ctx) (t : STerm) (τ : SType) : Result Unit :=
    match t with
    | abs n t1 =>
        match τ with
        | tfun τ1 τ2 => check (List.cons ⟨n, τ1⟩ Γ) t1 τ2
        | _ => inl $ wrong_type t τ
    | STerm.ite t1 t2 t3 =>
        all_right (check Γ t1 tbool) (check Γ t2 τ) (check Γ t3 τ)
    | _ => match synth Γ t with
           | inr τ1  => if τ == τ1
              then inr ()
              else inl $ "Incompatible types: expected '" ++ τ.toString ++ "' but got '" ++ τ1.toString ++ "'"
           | inl err => inl err

  partial def synth (Γ : Ctx) (t : STerm) : Result SType :=
    match t with
    | var n =>
        (Γ.lookup n).elim
          (λ () => inl $ "Unknown variable: " ++ toString n)
          (λ τ => inr τ)
    | app t1 t2 =>
        match synth Γ t1 with
        | inr (tfun τ1 τ2) => match check Γ t2 τ1 with
            | inr ()  => inr τ2
            | inl err => inl err
        | inr τ => inl $ expected_function t1 τ
        | err   => err
    | strue | sfalse => inr tbool
    | ann t1 τ => match check Γ t1 τ with
        | inr ()  => inr τ
        | inl err => inl err
    | _ => inl $ "No rules to synthesize a type for a term '" ++ t.toString ++ "'"
end

namespace examples

open STerm
open SType

instance : OfNat Name n where
  ofNat := n

-- λ f . λ g . λ b . g (f b) : (Bool → Bool) → (Bool → Bool) → Bool → Bool
def f : Name := 1
def g : Name := 2
def b : Name := 3
def body :=
  abs f (
    abs g (
      abs b (
        app (var g) (app (var f) (var b))
      )
    )
  )
def btob := tfun tbool tbool
def τ := tfun btob (tfun btob (tfun tbool tbool))
def ex1 := ann body τ

#eval synth [] ex1

def τ_wrong := tfun btob (tfun btob tbool)
def ex1_wrong := ann body τ_wrong

#eval synth [] ex1_wrong

end examples
