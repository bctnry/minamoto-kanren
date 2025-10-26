package main

import (
	"fmt"
	"maps"
	"slices"
	"strings"
)

const (
	VAR = 1
	VALUE = 2
	FUNCTOR = 3
)

type Term interface {
	Type() int
	String() string
}
type Var struct { Name string }
type Value struct { Value string }
type Functor struct {
	Head string
	Args []Term
}
func (v *Var) Type() int { return VAR; }
func (v *Value) Type() int { return VALUE; }
func (v *Functor) Type() int { return FUNCTOR; }
func (v *Var) String() string { return v.Name; }
func (v *Value) String() string { return v.Value; }
func (v *Functor) String() string {
	if len(v.Args) <= 0 { return v.Head }
	r := make([]string, 0)
	for _, v := range v.Args {
		r = append(r, v.String())
	}
	return fmt.Sprintf("%s(%s)", v.Head, strings.Join(r, ", "))
}


type State struct {
	Subst map[string]Term
	Gensym int
}

type Goal interface {
	Interpret(st *State) []*State
}
type Falsify struct {}
type Succeed struct {}
type Disjunction struct { A Goal; B Goal }
type Conjunction struct { A Goal; B Goal }
type Unify struct { Left Term; Right Term; }

func (_ *Falsify) Interpret(st *State) []*State {
	return make([]*State, 0)
}

func (_ *Succeed) Interpret(st *State) []*State {
	return []*State{ st }
}

func (dj *Disjunction) Interpret(st *State) []*State {
	return slices.Concat(
		dj.A.Interpret(st),
		dj.B.Interpret(st),
	)
}

func (cj *Conjunction) Interpret(st *State) []*State {
	s1 := cj.A.Interpret(st)
	if len(s1) <= 0 { return s1 }
	preres := make([]*State, 0)
	for _, v := range s1 {
		s2 := cj.B.Interpret(v)
		preres = slices.Concat(preres, s2)
	}
	return preres
}

func unify(_t1 Term, _t2 Term, st *State) *State {
	t1 := st.Lookup(_t1)
	t2 := st.Lookup(_t2)
	switch t1.Type() {
	case VALUE:
		switch t2.Type() {
		case VALUE:
			if t1.(*Value).Value == t2.(*Value).Value {
				return st
			} else {
				return nil
			}
		case VAR:
			return st.Extend(t2.(*Var).Name, t1)
		case FUNCTOR:
			return nil
		}
	case VAR:
		switch t2.Type() {
		case VAR:
			if t1.(*Var).Name == t2.(*Var).Name { return st }
			return st.Extend(t1.(*Var).Name, t2)
		default:
			return st.Extend(t1.(*Var).Name, t2)
		}
	case FUNCTOR:
		switch t2.Type() {
		case VALUE:
			return nil
		case VAR:
			return st.Extend(t2.(*Var).Name, t1)
		case FUNCTOR:
			a := t1.(*Functor)
			b := t2.(*Functor)
			if a.Head != b.Head { return nil }
			if len(a.Args) != len(b.Args) { return nil }
			return unifyMany(a.Args, b.Args, st)
		}
	}
	return nil
}

func unifyMany(t1 []Term, t2 []Term, st *State) *State {
	s := st
	if s == nil { return nil }
	for i := range len(t1) {
		s = unify(t1[i], t2[i], s)
		if s == nil { return nil }
	}
	return s
}

func (u *Unify) Interpret(st *State) []*State {
	ures := unify(u.Left, u.Right, st)
	if ures == nil { return []*State{} }
	return []*State{ ures }
}

func (st *State) Extend(varName string, t Term) *State {
	mm := maps.Clone(st.Subst)
	mm[varName] = t
	return &State{ Subst: mm, Gensym: st.Gensym }
}

func (st *State) Lookup(t Term) Term {
	switch t.Type() {
	case VAR:
		v, ok := st.Subst[t.(*Var).Name]
		if !ok { return t }
		return v
	default:
		return t
	}
}

func (st *State) Fresh() Term {
	res := &Var{ Name: fmt.Sprintf("V_%d", st.Gensym) }
	st.Gensym += 1
	return res
}

func Run(g Goal) []*State {
	return g.Interpret(&State{
		Subst: make(map[string]Term, 0),
		Gensym: 0,
	})
}

func choice(out Term, scope []Term) Goal {
	if len(scope) <= 0 { return &Falsify{} }
	if len(scope) == 1 { return &Unify{ Left: out, Right: scope[0] } }
	var subj Goal
	subj = &Unify{ Left: out, Right: scope[len(scope)-1] }
	i := len(scope)-2
	for i >= 0 {
		subj = &Disjunction{
			A: &Unify{ Left: out, Right: scope[i] },
			B: subj,
		}
		i -= 1
	}
	return subj
}

func SubstToString(sub map[string]Term) string {
	res := make([]string, 0)
	for k, v := range sub {
		res = append(res, fmt.Sprintf("%s->%s", k, v.String()))
	}
	return fmt.Sprintf("{%s}", strings.Join(res, ","))
}

func (st *State) String() string {
	return fmt.Sprintf("<%s,%d>", SubstToString(st.Subst), st.Gensym)
}

func cons(t1 Term, t2 Term) Term {
	return &Functor{ Head: "cons", Args: []Term{ t1, t2 } }
}
func emtpyList() Term {
	return &Functor{ Head: "nil", Args: []Term{} }
}

func conso(t1 Term, t2 Term, t3 Term) Goal {
	return &Unify{ Left: cons(t1, t2), Right: t3 }
}

func conjN(gl []Goal) Goal {
	if len(gl) <= 0 { return &Succeed{} }
	if len(gl) == 1 { return gl[0] }
	subj := gl[len(gl)-1]
	i := len(gl)-2
	for i >= 0 {
		subj = &Conjunction{ A: gl[i], B: subj }
		i -= 1
	}
	return subj
}

// the thing is that we've chosen to use first-order construct only
// so that the whole idea could be easily replicated in languages like C.
// appendo here cannot be implemented as a goal builder anymore, since
// we need to access the state to generate fresh logic variables and
// the only way we can gain access to the state is by doing this.
// i don't think this corresponds to the eta-expansion required in
// the scheme version of sokuza kanren since we do everything first-order
// and thus don't have the problem caused by eager evaluation, but i
// may be wrong on this front.
type AppendO struct { L1, L2, L3 Term }
func (f *AppendO) Interpret(st *State) []*State {
	h := st.Fresh()
	t := st.Fresh()
	l3p := st.Fresh()
	return (&Disjunction{
		A: &Conjunction{
			A: &Unify{ Left: f.L1, Right: emtpyList() },
			B: &Unify{ Left: f.L2, Right: f.L3 },
		},
		B: conjN([]Goal{
			conso(h, t, f.L1),
			conso(h, l3p, f.L3),
			&AppendO{ L1: t, L2: f.L2, L3: l3p },
		}),
	}).Interpret(st)
}

func (st *State) LookupN(t Term) Term {
	switch t.Type() {
	case VAR:
		v, ok := st.Subst[t.(*Var).Name]
		if !ok { return t }
		switch v.Type() {
		case VAR:
			return v
		case VALUE:
			return v
		case FUNCTOR:
			foundArgs := make([]Term, 0)
			for _, a := range v.(*Functor).Args {
				foundArgs = append(foundArgs, st.LookupN(a))
			}
			return &Functor{
				Head: v.(*Functor).Head,
				Args: foundArgs,
			}
		default:
			panic("invalid")
		}
	default:
		return t
	}
}

func value(s string) *Value { return &Value{Value: s} }
func mkvar(s string) *Var { return &Var{Name: s} }

func main() {
	vq := mkvar("Q")
	g := &AppendO{
		L1: vq,
		L2: mkvar("X"),
		L3: cons(value("1"), cons(value("2"), cons(value("3"), emtpyList()))),
	}
	res := g.Interpret(&State{
		Subst: make(map[string]Term, 0),
		Gensym: 0,
	})
	for k, v := range res {
		fmt.Printf("solution %d: %s\n", k, v.LookupN(vq))
	}
}

