// {{{ MIT License

// Copyright 2017 Roland Kaminski

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.

// }}}

#ifndef GRINGO_TERM_HH
#define GRINGO_TERM_HH

#include <gringo/bug.hh>
#include <gringo/symbol.hh>
#include <gringo/printable.hh>
#include <gringo/hashable.hh>
#include <gringo/locatable.hh>
#include <gringo/comparable.hh>
#include <gringo/clonable.hh>
#include <gringo/utility.hh>
#include <gringo/logger.hh>
#include <memory>
#include <unordered_set>
#ifdef _MSC_VER
#pragma warning( push )
#pragma warning( disable : 4503 ) // decorated name length exceeded
#pragma warning( disable : 4521 ) // multiple copy constructors specified
#endif
namespace Gringo {

// {{{ declaration of UnOp and BinOp

enum class BinOp : int { XOR, OR, AND, ADD, SUB, MUL, DIV, MOD, POW };
enum class UnOp : int { NEG, NOT, ABS };

int eval(UnOp op, int x);
int eval(BinOp op, int x, int y);

std::ostream &operator<<(std::ostream &out, BinOp op);
std::ostream &operator<<(std::ostream &out, UnOp op);

// }}}

 // {{{ declaration of Defines

class Term;
using UTerm = std::unique_ptr<Term>;

class Defines {
public:
    using DefMap = std::unordered_map<String, std::tuple<bool, Location, UTerm>>;
    Defines() = default;
    Defines(Defines const &other) = delete;
    Defines(Defines &&other) noexcept = delete;
    Defines &operator=(Defines const &other) = delete;
    Defines &operator=(Defines &&other) noexcept = delete;
    ~Defines() noexcept = default;

    //! Add a define.
    //! Default defintions will not overwrite existing definitions and can be overwritten by other defines.
    void add(Location const &loc, String name, UTerm &&value, bool defaultDef, Logger &log);
    //! Evaluates layered definitions and checks for cycles.
    void init(Logger &log);
    bool empty() const;
    void apply(Symbol x, Symbol &retVal, UTerm &retTerm, bool replace);
    DefMap const &defs() const;

private:
    std::unordered_map<String, std::tuple<bool, Location, UTerm>> defs_;
};

// }}}

// {{{ declaration of GTerm

struct GRef;
class GTerm;
class GVarTerm;
class GFunctionTerm;
class GLinearTerm;
using UGTerm = std::unique_ptr<GTerm>;
using UGFunTerm = std::unique_ptr<GFunctionTerm>;
class GTerm : public Clonable<GTerm>, public Printable, public Hashable, public Comparable<GTerm> {
public:
    using EvalResult = std::pair<bool, Symbol>;

    GTerm() = default;
    GTerm(GTerm const &other) = default;
    GTerm(GTerm &&other) noexcept = default;
    GTerm &operator=(GTerm const &other) = default;
    GTerm &operator=(GTerm &&other) noexcept = default;
    ~GTerm() noexcept override = default;

    virtual Sig sig() const = 0;
    virtual EvalResult eval() const = 0;
    virtual bool occurs(GRef &x) const = 0;
    virtual void reset() = 0;
    virtual bool match(Symbol const &x) = 0;
    virtual bool unify(GTerm &x) = 0;
    virtual bool unify(GFunctionTerm &x) = 0;
    virtual bool unify(GLinearTerm &x) = 0;
    virtual bool unify(GVarTerm &x) = 0;
};
using UGTermVec = std::vector<UGTerm>;
using SGRef     = std::shared_ptr<GRef>;

// }}}
// {{{ declaration of Term

class LinearTerm;
class VarTerm;
class ValTerm;
using UTermVec        = std::vector<UTerm>;
using UTermVecVec     = std::vector<UTermVec>;
using VarTermVec      = std::vector<std::reference_wrapper<VarTerm>>;
using VarTermBoundVec = std::vector<std::pair<VarTerm*,bool>>;
using VarTermSet      = std::unordered_set<std::reference_wrapper<VarTerm>, value_hash<std::reference_wrapper<VarTerm>>, value_equal_to<std::reference_wrapper<VarTerm>>>;

class AuxGen {
public:
    AuxGen()
    : auxNum(std::make_shared<unsigned>(0)) { }
    AuxGen(AuxGen const &other) = default;
    AuxGen(AuxGen &&other) noexcept = default;
    AuxGen &operator=(AuxGen const &other) = default;
    AuxGen &operator=(AuxGen &&other) noexcept = default;
    ~AuxGen() noexcept = default;

    String uniqueName(char const *prefix);
    UTerm uniqueVar(Location const &loc, unsigned level, const char *prefix);

private:
    std::shared_ptr<unsigned> auxNum;
};

class SimplifyState {
public:
    //! Somewhat complex result type of simplify.
    class SimplifyRet;

    //! Type that stores for each rewritten DotsTerm the associated variable and the lower and upper bound.
    using DotsMap = std::vector<std::tuple<UTerm, UTerm, UTerm>>;
    using ScriptMap = std::vector<std::tuple<UTerm, String, UTermVec>>;

    SimplifyState() = default;
    SimplifyState(SimplifyState const &other) = delete;
    SimplifyState(SimplifyState &&other) noexcept = default;
    SimplifyState &operator=(SimplifyState const &other) = delete;
    SimplifyState &operator=(SimplifyState &&other) noexcept = default;
    ~SimplifyState() noexcept = default;

    static SimplifyState make_substate(SimplifyState &state) {
        return {state.gen_, state.level_ + 1};
    }

    String createName(char const *prefix);
    std::unique_ptr<LinearTerm> createDots(Location const &loc, UTerm &&left, UTerm &&right);
    SimplifyRet createScript(Location const &loc, String name, UTermVec &&args, bool arith);

    DotsMap dots() {
        return std::move(dots_);
    }
    ScriptMap scripts() {
        return std::move(scripts_);
    }

private:
    SimplifyState(AuxGen &gen, int level)
    : gen_{gen}
    , level_{level} { }

    DotsMap dots_;
    ScriptMap scripts_;
    AuxGen gen_;
    int level_{0};
};

class Term : public Printable, public Hashable, public Locatable, public Comparable<Term>, public Clonable<Term> {
public:
    //! Return value of Term::project (replace, projected, project).
    //! replace:   projected variables are stripped, null if untouched
    //! projected: term with variables renamed, projected if null
    //! project:   term with variables renamed, never null
    using ProjectRet   = std::tuple<UTerm, UTerm, UTerm>;
    using SVal         = std::shared_ptr<Symbol>;
    using VarSet       = std::unordered_set<String>;
    using RenameMap    = std::unordered_map<String, std::pair<String, SVal>>;
    using ReferenceMap = std::unordered_map<Term*, SGRef, value_hash<Term*>, value_equal_to<Term*>>;
    using SimplifyRet  = SimplifyState::SimplifyRet;
    //! Type that stores for each rewritten arithmetic term (UnopTerm, BinopTerm, LuaTerm) the associated variable and the term itself.
    //! The indices of the vector correspond to the level of the term.
    using LevelMap = std::unordered_map<UTerm, UTerm, value_hash<UTerm>, value_equal_to<UTerm>>;
    using ArithmeticsMap = std::vector<std::unique_ptr<LevelMap>>;
    //! The invertibility of a term. This may either be
    //! - CONSTANT for terms that do not contain variables,
    //! - INVERTIBLE for invertible terms (e.g. -X, 1+X, f(X,Y+Z))
    //! - NOT_INVERTIBLE for terms that are not invertible (e.g. arithmetic operations with two unknowns)
    enum Invertibility { CONSTANT = 0, INVERTIBLE = 1, NOT_INVERTIBLE = 2 };

    Term() = default;
    Term(Term const &other) = default;
    Term(Term &&other) noexcept = default;
    Term &operator=(Term const &other) = default;
    Term &operator=(Term &&other) noexcept = default;
    ~Term() noexcept override = default;

    //! Whether the term contains a VarTerm.
    virtual bool hasVar() const = 0;
    virtual unsigned projectScore() const = 0;
    //! Rename the outermost term.
    //! \pre the term must either be a function term or value term holding an identifier.
    //! \note unnecessary; can be deleted
    virtual void rename(String name) = 0;
    //! Removes all occurrences of PoolTerm instances.
    //! Returns all unpooled incarnations of the term.
    //! \note The term becomes unusable after the method returns.
    //! \post The pool does not contain PoolTerm instances.
    virtual void unpool(UTermVec &x) const = 0;
    //! Removes all occurrences of DotsTerm instances, simplifies the term and sets the invertibility.
    //! To reduce the number of cases in later algorithms moves invertible terms to the left:
    //! - 1+X -> X+1
    //! - (1+(1-X)) -> ((-X)+1)+1
    //! Replaces undefined arithmetic operations with 0:
    //! - f(X)+0 -> 0
    //! \note The term is unusable if the method returned a non-zero replacement term.
    //! \pre Must be called after unpool.
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log) = 0;
    //! Removes anonymous variables in projectable positions (in outermost function symbols) from a term.
    //! The first element of the return value is a replacement term for the current term,
    //! which might be null if the term does not have to be replace..
    //! The second and third can be used to create a projection rule
    //! where the second is the head and the third is the body element.
    //! \pre Must be called after simplify.
    //! \code{.cpp}
    //! num = 0; sig = base; lit = q(X,_)
    //! (lit', projected, project) = lit.project(&sig, num)
    //! assert(lit'      == #p_q(base,X,#p))
    //! assert(projected == #p_q(base,#X1,#p))
    //! assert(project   == #p_q(base,#X1,#Y2))
    //! \endcode
    virtual ProjectRet project(bool rename, AuxGen &gen) = 0;
    //! Obtain the type of a term.
    //! \pre Must be called after simplify.
    //! Whether evaluation of a term is guaranteed to not produce numeric values.
    //! This means that the term is either a non-numeric constant or a function symbol.
    virtual bool isNotNumeric() const = 0;
    virtual bool isNotFunction() const = 0;
    //! Obtain the invertibility of a term.
    //! \pre Must be called after simplify.
    virtual Invertibility getInvertibility() const = 0;
    //! Evaluates the term to a value.
    //! \pre Must be called after simplify.
    virtual Symbol eval(bool &undefined, Logger &log) const = 0;
    //! Returns true if the term evaluates to zero.
    //! \pre Must be called after simplify.
    //! \pre Term is ground or
    bool isZero(Logger &log) const;
    //! Collects variables in Terms.
    //! \pre Must be called after simplify and project to properly account for bound variables.
    // TODO: the way I am using these it would be nice to have a visitor for variables
    //       and implement the functions below using the visitor
    virtual void collect(VarTermBoundVec &vars, bool bound) const = 0;
    virtual void collect(VarTermSet &vars) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const = 0;
    virtual void collectIds(VarSet &vars) const = 0;
    //! Returns the nesting level of a term.
    //! That is the largest level of a nested variable or zero for ground terms.
    //! \pre Must be called after assignLevel.
    virtual unsigned getLevel() const = 0;
    //! Removes non-invertible arithmetics.
    //! \note The term is unusable if the method returned a non-zero replacement term.
    //! \pre Must be called after assignLevel.
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined = false) = 0;
    virtual bool match(Symbol const &val) const = 0;
    bool bind(VarSet &bound) const;
    virtual Sig getSig() const = 0;
    virtual UTerm renameVars(RenameMap &names) const = 0;
    SGRef _newRef(RenameMap &names, ReferenceMap &refs) const;
    UGTerm gterm() const;
    virtual UGFunTerm gfunterm(RenameMap &names, ReferenceMap &refs) const;
    virtual bool hasPool() const = 0;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const = 0;
    virtual UTerm replace(Defines &defs, bool replace) = 0;
    virtual double estimate(double size, VarSet const &bound) const = 0;
    virtual Symbol isEDB() const = 0;
    virtual int toNum(bool &undefined, Logger &log);
    virtual bool isAtom() const { return false; }

    //! Inserts a term into arith creating a new unique variable if necessary.
    static UTerm insert(ArithmeticsMap &arith, AuxGen &auxGen, UTerm &&term, bool eq = false);

    //! Set dst to src if src is non-zero.
    template <class T, class U>
    static void replace(std::unique_ptr<T> &dst, std::unique_ptr<U> &&src);
    template <class T, class U, class V>
    void replace(std::unique_ptr<T> &dst, std::unique_ptr<U> &&src, std::unique_ptr<V> &&alt);

    //! Unpools a, calling g on each obtained element.
    template <class A, class UnpoolA, class Callback>
    static void unpool(A const &a, UnpoolA const &fA, Callback const &g);
    //! Unpools a  and b, calculates cross product, calling g on each obtained tuple.
    template <class A, class B, class UnpoolA, class UnpoolB, class Callback>
    static void unpool(A const &a, B const &b, UnpoolA const &fA, UnpoolB const &fB, Callback const &g);
    //! Iterates of [begin, end] unpooling with f, calculates cross product, calling g on each obtained tuple.
    template <class It, class Unpool, class Callback>
    static void unpool(It const &begin, It const &end, Unpool const &f, Callback const &g);
    //! Unpools each element of vec using f, and move the union of all pools back to f.
    template <class Vec, class Unpool>
    static void unpoolJoin(Vec &vec, Unpool const &f);
};

UTermVec unpool(UTerm const &x);

class LinearTerm;
class SimplifyState::SimplifyRet {
public:
    enum Type { UNTOUCHED, CONSTANT, LINEAR, REPLACE, UNDEFINED };

    //! Reference to untouched term.
    SimplifyRet(Term &x, bool project);
    //! Indicate replacement with linear term.
    SimplifyRet(std::unique_ptr<LinearTerm> &&x);
    //! Indicate replacement with arbitrary term.
    SimplifyRet(UTerm &&x);
    //! Indicate replacement with value.
    SimplifyRet(Symbol const &x);
    //! Indicate undefined term
    SimplifyRet();
    SimplifyRet(SimplifyRet const &) = delete;
    SimplifyRet(SimplifyRet &&x) noexcept;
    SimplifyRet &operator=(SimplifyRet const &) = delete;
    SimplifyRet &operator=(SimplifyRet &&x) noexcept;
    ~SimplifyRet() noexcept;

    bool notNumeric() const;
    bool notFunction() const;
    bool constant() const;
    bool isZero() const;
    bool undefined() const;
    LinearTerm &lin() const;
    SimplifyRet &update(UTerm &x, bool arith);
    Type type() const {
        return type_;
    }
    Symbol value() const {
        return val_; // NOLINT
    }
    bool project() const {
        return project_;
    }

private:
    Type  type_;
    bool  project_ = false;
    union { // NOLINT
        Symbol val_;
        Term *term_;
    };
};

// }}}

// {{{ declaration of GRef

struct GRef {
    enum Type { EMPTY, VALUE, TERM };
    GRef(UTerm &&name);
    operator bool() const;
    void reset();
    GRef &operator=(Symbol const &x);
    GRef &operator=(GTerm &x);
    bool occurs(GRef &x) const;
    bool match(Symbol const &x) const;
    template <class T>
    bool unify(T &x);

    Type        type;
    UTerm       name;
    // Note: these two could be put into a union
    Symbol       value;
    GTerm      *term;
};
using SGRef = std::shared_ptr<GRef>;

// }}}
// {{{ declaration of GValTerm

class GValTerm : public GTerm {
public:
    GValTerm(Symbol val);
    GValTerm(GValTerm const &other) = default;
    GValTerm(GValTerm &&other) noexcept = default;
    GValTerm &operator=(GValTerm const &other) = default;
    GValTerm &operator=(GValTerm &&other) noexcept = default;
    ~GValTerm() noexcept override = default;

    bool operator==(GTerm const &other) const override;
    size_t hash() const override;
    void print(std::ostream &out) const override;
    Sig sig() const override;
    EvalResult eval() const override;
    bool occurs(GRef &x) const override;
    void reset() override;
    bool match(Symbol const &x) override;
    bool unify(GTerm &x) override;
    bool unify(GFunctionTerm &x) override;
    bool unify(GLinearTerm &x) override;
    bool unify(GVarTerm &x) override;
    GValTerm *clone() const override {
        return new GValTerm{val_}; // NOLINT
    }

private:
    Symbol val_;
};

// }}}
// {{{ declaration of GFunctionTerm

class GFunctionTerm : public GTerm {
public:
    GFunctionTerm(String name, UGTermVec &&args);
    GFunctionTerm(GFunctionTerm const &x, bool sign);
    GFunctionTerm(GFunctionTerm const &other) = default;
    GFunctionTerm(GFunctionTerm &&other) noexcept = default;
    GFunctionTerm &operator=(GFunctionTerm const &other) = default;
    GFunctionTerm &operator=(GFunctionTerm &&other) noexcept = default;
    ~GFunctionTerm() noexcept override = default;

    void flipSign() { sign_ = !sign_; }

    bool operator==(GTerm const &other) const override;
    size_t hash() const override;
    void print(std::ostream &out) const override;
    Sig sig() const override;
    EvalResult eval() const override;
    bool occurs(GRef &x) const override;
    void reset() override;
    bool match(Symbol const &x) override;
    bool unify(GTerm &x) override;
    bool unify(GFunctionTerm &x) override;
    bool unify(GLinearTerm &x) override;
    bool unify(GVarTerm &x) override;
    GFunctionTerm *clone() const override {
        auto *ret = new GFunctionTerm{name_, get_clone(args_)};
        ret->sign_ = sign_;
        return ret;
    }

private:
    bool sign_;
    String name_;
    UGTermVec args_;
};

// }}}
// {{{ declaration of GLinearTerm

class GLinearTerm : public GTerm {
public:
    GLinearTerm(const SGRef& ref, int m, int n);
    GLinearTerm(GLinearTerm const &other) = default;
    GLinearTerm(GLinearTerm &&other) noexcept = default;
    GLinearTerm &operator=(GLinearTerm const &other) = default;
    GLinearTerm &operator=(GLinearTerm &&other) noexcept = default;
    ~GLinearTerm() noexcept override = default;

    bool operator==(GTerm const &other) const override;
    size_t hash() const override;
    void print(std::ostream &out) const override;
    Sig sig() const override;
    EvalResult eval() const override;
    bool occurs(GRef &x) const override;
    void reset() override;
    bool match(Symbol const &x) override;
    bool unify(GTerm &x) override;
    bool unify(GFunctionTerm &x) override;
    bool unify(GLinearTerm &x) override;
    bool unify(GVarTerm &x) override;
    GLinearTerm *clone() const override {
        return new GLinearTerm{ref_, m_, n_}; // NOLINT
    }

private:
    SGRef ref_;
    int m_;
    int n_;
};

// }}}
// {{{ declaration of GVarTerm

class GVarTerm : public GTerm {
public:
    GVarTerm(const SGRef& ref);
    GVarTerm(GVarTerm const &other) = default;
    GVarTerm(GVarTerm &&other) noexcept = default;
    GVarTerm &operator=(GVarTerm const &other) = default;
    GVarTerm &operator=(GVarTerm &&other) noexcept = default;
    ~GVarTerm() noexcept override = default;


    bool operator==(GTerm const &other) const override;
    size_t hash() const override;
    void print(std::ostream &out) const override;
    Sig sig() const override;
    EvalResult eval() const override;
    bool occurs(GRef &x) const override;
    void reset() override;
    bool match(Symbol const &x) override;
    bool unify(GTerm &x) override;
    bool unify(GFunctionTerm &x) override;
    bool unify(GLinearTerm &x) override;
    bool unify(GVarTerm &x) override;
    GVarTerm *clone() const override {
        return new GVarTerm{ref}; // NOLINT
    }

    SGRef ref;
};

// }}}

// {{{ declaration of PoolTerm

class PoolTerm : public Term {
public:
    PoolTerm(UTermVec &&terms);
    ~PoolTerm() noexcept override = default;

    virtual unsigned projectScore() const;
    virtual void rename(String name);
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log);
    virtual ProjectRet project(bool rename, AuxGen &gen);
    virtual bool hasVar() const;
    virtual void collect(VarTermBoundVec &vars, bool bound) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const;
    virtual Symbol eval(bool &undefined, Logger &log) const;
    virtual bool match(Symbol const &val) const;
    virtual Sig getSig() const;
    virtual UTerm renameVars(RenameMap &names) const;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const;
    virtual unsigned getLevel() const;
    virtual bool isNotNumeric() const;
    virtual bool isNotFunction() const;
    virtual Invertibility getInvertibility() const;
    virtual void print(std::ostream &out) const;
    virtual void unpool(UTermVec &x) const;
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined);
    virtual bool operator==(Term const &other) const;
    virtual size_t hash() const;
    virtual PoolTerm *clone() const;
    virtual bool hasPool() const;
    virtual void collectIds(VarSet &vars) const;
    virtual UTerm replace(Defines &defs, bool replace = true);
    virtual double estimate(double size, VarSet const &bound) const;
    virtual Symbol isEDB() const;
    virtual bool isAtom() const;

private:
    UTermVec args;
};

// }}}
// {{{ declaration of ValTerm

class ValTerm : public Term {
public:
    ValTerm(Symbol value);
    ~ValTerm() noexcept override = default;

    virtual unsigned projectScore() const;
    virtual void rename(String name);
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log);
    virtual ProjectRet project(bool rename, AuxGen &gen);
    virtual bool hasVar() const;
    virtual void collect(VarTermBoundVec &vars, bool bound) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const;
    virtual Symbol eval(bool &undefined, Logger &log) const;
    virtual bool match(Symbol const &val) const;
    virtual Sig getSig() const;
    virtual UTerm renameVars(RenameMap &names) const;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const;
    virtual unsigned getLevel() const;
    virtual bool isNotNumeric() const;
    virtual bool isNotFunction() const;
    virtual Invertibility getInvertibility() const;
    virtual void print(std::ostream &out) const;
    virtual void unpool(UTermVec &x) const;
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined);
    virtual bool operator==(Term const &other) const;
    virtual size_t hash() const;
    virtual ValTerm *clone() const;
    virtual bool hasPool() const;
    virtual void collectIds(VarSet &vars) const;
    virtual UTerm replace(Defines &defs, bool replace = true);
    virtual double estimate(double size, VarSet const &bound) const;
    virtual Symbol isEDB() const;
    virtual bool isAtom() const;

private:
    Symbol value;
};

// }}}
// {{{ declaration of VarTerm

class VarTerm : public Term {
public:
    VarTerm(String name, const SVal& ref, unsigned level = 0, bool bindRef = false);
    virtual unsigned projectScore() const;
    virtual void rename(String name);
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log);
    virtual ProjectRet project(bool rename, AuxGen &gen);
    virtual bool hasVar() const;
    virtual void collect(VarTermBoundVec &vars, bool bound) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const;
    virtual Symbol eval(bool &undefined, Logger &log) const;
    virtual bool match(Symbol const &val) const;
    virtual Sig getSig() const;
    virtual UTerm renameVars(RenameMap &names) const;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const;
    virtual unsigned getLevel() const;
    virtual bool isNotNumeric() const;
    virtual bool isNotFunction() const;
    virtual Invertibility getInvertibility() const;
    virtual void print(std::ostream &out) const;
    virtual void unpool(UTermVec &x) const;
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined);
    virtual bool operator==(Term const &other) const;
    virtual size_t hash() const;
    virtual VarTerm *clone() const;
    virtual bool hasPool() const;
    virtual void collectIds(VarSet &vars) const;
    virtual UTerm replace(Defines &defs, bool replace = true);
    virtual double estimate(double size, VarSet const &bound) const;
    virtual Symbol isEDB() const;
    virtual ~VarTerm() noexcept = default;

    String name;
    SVal ref;
    bool bindRef;
    unsigned level;
};

// }}}
// {{{ declaration of UnOpTerm

class UnOpTerm : public Term {
public:
    UnOpTerm(UnOp op, UTerm &&arg);
    ~UnOpTerm() noexcept override = default;

    virtual unsigned projectScore() const;
    virtual void rename(String name);
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log);
    virtual ProjectRet project(bool rename, AuxGen &gen);
    virtual bool hasVar() const;
    virtual void collect(VarTermBoundVec &vars, bool bound) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const;
    virtual Symbol eval(bool &undefined, Logger &log) const;
    virtual bool match(Symbol const &val) const;
    virtual Sig getSig() const;
    virtual UTerm renameVars(RenameMap &names) const;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const;
    virtual UGFunTerm gfunterm(RenameMap &names, ReferenceMap &refs) const;
    virtual unsigned getLevel() const;
    virtual bool isNotNumeric() const;
    virtual bool isNotFunction() const;
    virtual Invertibility getInvertibility() const;
    virtual void print(std::ostream &out) const;
    virtual void unpool(UTermVec &x) const;
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined);
    virtual bool operator==(Term const &other) const;
    virtual size_t hash() const;
    virtual UnOpTerm *clone() const;
    virtual bool hasPool() const;
    virtual void collectIds(VarSet &vars) const;
    virtual UTerm replace(Defines &defs, bool replace = true);
    virtual double estimate(double size, VarSet const &bound) const;
    virtual Symbol isEDB() const;
    virtual bool isAtom() const;

private:
    UnOp const op;
    UTerm arg;
};

// }}}
// {{{ declaration of BinOpTerm

class BinOpTerm : public Term {
public:
    BinOpTerm(BinOp op, UTerm &&left, UTerm &&right);
    ~BinOpTerm() noexcept override = default;

    virtual unsigned projectScore() const;
    virtual void rename(String name);
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log);
    virtual ProjectRet project(bool rename, AuxGen &gen);
    virtual bool hasVar() const;
    virtual void collect(VarTermBoundVec &vars, bool bound) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const;
    virtual Symbol eval(bool &undefined, Logger &log) const;
    virtual bool match(Symbol const &val) const;
    virtual Sig getSig() const;
    virtual UTerm renameVars(RenameMap &names) const;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const;
    virtual unsigned getLevel() const;
    virtual bool isNotNumeric() const;
    virtual bool isNotFunction() const;
    virtual Invertibility getInvertibility() const;
    virtual void print(std::ostream &out) const;
    virtual void unpool(UTermVec &x) const;
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined);
    virtual bool operator==(Term const &other) const;
    virtual size_t hash() const;
    virtual BinOpTerm *clone() const;
    virtual bool hasPool() const;
    virtual void collectIds(VarSet &vars) const;
    virtual UTerm replace(Defines &defs, bool replace = true);
    virtual double estimate(double size, VarSet const &bound) const;
    virtual Symbol isEDB() const;

private:
    BinOp op;
    UTerm left;
    UTerm right;
};

// }}}
// {{{ declaration of DotsTerm

class DotsTerm : public Term {
public:
    DotsTerm(UTerm &&left, UTerm &&right);
    ~DotsTerm() noexcept override = default;

    virtual unsigned projectScore() const;
    virtual void rename(String name);
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log);
    virtual ProjectRet project(bool rename, AuxGen &gen);
    virtual bool hasVar() const;
    virtual void collect(VarTermBoundVec &vars, bool bound) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const;
    virtual Symbol eval(bool &undefined, Logger &log) const;
    virtual bool match(Symbol const &val) const;
    virtual Sig getSig() const;
    virtual UTerm renameVars(RenameMap &names) const;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const;
    virtual unsigned getLevel() const;
    virtual bool isNotNumeric() const;
    virtual bool isNotFunction() const;
    virtual Invertibility getInvertibility() const;
    virtual void print(std::ostream &out) const;
    virtual void unpool(UTermVec &x) const;
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined);
    virtual bool operator==(Term const &other) const;
    virtual size_t hash() const;
    virtual DotsTerm *clone() const;
    virtual bool hasPool() const;
    virtual void collectIds(VarSet &vars) const;
    virtual UTerm replace(Defines &defs, bool replace = true);
    virtual double estimate(double size, VarSet const &bound) const;
    virtual Symbol isEDB() const;

private:
    UTerm left;
    UTerm right;
};

// }}}
// {{{ declaration of LuaTerm

class LuaTerm : public Term {
public:
    LuaTerm(String name, UTermVec &&args);
    ~LuaTerm() noexcept override = default;

    virtual unsigned projectScore() const;
    virtual void rename(String name);
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log);
    virtual ProjectRet project(bool rename, AuxGen &gen);
    virtual bool hasVar() const;
    virtual void collect(VarTermBoundVec &vars, bool bound) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const;
    virtual Symbol eval(bool &undefined, Logger &log) const;
    virtual bool match(Symbol const &val) const;
    virtual Sig getSig() const;
    virtual UTerm renameVars(RenameMap &names) const;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const;
    virtual unsigned getLevel() const;
    virtual bool isNotNumeric() const;
    virtual bool isNotFunction() const;
    virtual Invertibility getInvertibility() const;
    virtual void print(std::ostream &out) const;
    virtual void unpool(UTermVec &x) const;
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined);
    virtual bool operator==(Term const &other) const;
    virtual size_t hash() const;
    virtual LuaTerm *clone() const;
    virtual bool hasPool() const;
    virtual void collectIds(VarSet &vars) const;
    virtual UTerm replace(Defines &defs, bool replace = true);
    virtual double estimate(double size, VarSet const &bound) const;
    virtual Symbol isEDB() const;

private:
    String const name;
    UTermVec args;
};

// }}}
// {{{ declaration of FunctionTerm

class FunctionTerm : public Term {
public:
    FunctionTerm(String name, UTermVec &&args);
    ~FunctionTerm() noexcept = default;

    UTermVec const &arguments() {
        return args;
    };

    virtual unsigned projectScore() const;
    virtual void rename(String name);
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log);
    virtual ProjectRet project(bool rename, AuxGen &gen);
    virtual bool hasVar() const;
    virtual void collect(VarTermBoundVec &vars, bool bound) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const;
    virtual Symbol eval(bool &undefined, Logger &log) const;
    virtual bool match(Symbol const &val) const;
    virtual Sig getSig() const;
    virtual UTerm renameVars(RenameMap &names) const;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const;
    virtual UGFunTerm gfunterm(RenameMap &names, ReferenceMap &refs) const;
    virtual unsigned getLevel() const;
    virtual bool isNotNumeric() const;
    virtual bool isNotFunction() const;
    virtual Invertibility getInvertibility() const;
    virtual void print(std::ostream &out) const;
    virtual void unpool(UTermVec &x) const;
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined);
    virtual bool operator==(Term const &other) const;
    virtual size_t hash() const;
    virtual FunctionTerm *clone() const;
    virtual bool hasPool() const;
    virtual void collectIds(VarSet &vars) const;
    virtual UTerm replace(Defines &defs, bool replace = true);
    virtual double estimate(double size, VarSet const &bound) const;
    virtual Symbol isEDB() const;
    virtual bool isAtom() const;

private:
    String name;
    UTermVec args;
    mutable SymVec cache;
};

// }}}
// {{{ declaration of LinearTerm

// TODO: if it holds a var it can as well use its location
class LinearTerm : public Term {
public:
    using UVarTerm = std::unique_ptr<VarTerm>;
    LinearTerm(VarTerm const &var, int m, int n);
    LinearTerm(UVarTerm &&var, int m, int n);
    ~LinearTerm() noexcept override = default;

    bool isVar() const { return m == 1 && n == 0; }
    UVarTerm toVar() { return std::move(var); }
    void invert() {
        m *= -1;
        n *= -1;
    }
    void add(int c) {
        n += c;
    }
    void mul(int c) {
        m *= c;
        n *= c;
    }

    virtual unsigned projectScore() const;
    virtual void rename(String name);
    virtual SimplifyRet simplify(SimplifyState &state, bool positional, bool arithmetic, Logger &log);
    virtual ProjectRet project(bool rename, AuxGen &gen);
    virtual bool hasVar() const;
    virtual void collect(VarTermBoundVec &vars, bool bound) const;
    virtual void collect(VarSet &vars, unsigned minLevel = 0, unsigned maxLevel = std::numeric_limits<unsigned>::max()) const;
    virtual Symbol eval(bool &undefined, Logger &log) const;
    virtual bool match(Symbol const &val) const;
    virtual Sig getSig() const;
    virtual UTerm renameVars(RenameMap &names) const;
    virtual UGTerm gterm(RenameMap &names, ReferenceMap &refs) const;
    virtual unsigned getLevel() const;
    virtual bool isNotNumeric() const;
    virtual bool isNotFunction() const;
    virtual Invertibility getInvertibility() const;
    virtual void print(std::ostream &out) const;
    virtual void unpool(UTermVec &x) const;
    virtual UTerm rewriteArithmetics(ArithmeticsMap &arith, AuxGen &auxGen, bool forceDefined);
    virtual bool operator==(Term const &other) const;
    virtual size_t hash() const;
    virtual LinearTerm *clone() const;
    virtual bool hasPool() const;
    virtual void collectIds(VarSet &vars) const;
    virtual UTerm replace(Defines &defs, bool replace = true);
    virtual double estimate(double size, VarSet const &bound) const;
    virtual Symbol isEDB() const;

private:
    UVarTerm var;
    int m;
    int n;
};

// }}}

// {{{ definition of Term and auxiliary functions

// TODO: ugly

template <class T, class U>
void Term::replace(std::unique_ptr<T> &dst, std::unique_ptr<U> &&src) {
    if (src) { dst = std::move(src); }
}

template <class A, class UnpoolA, class Callback>
void Term::unpool(A const &a, UnpoolA const &fA, Callback const &g) {
    for (auto &termA : fA(a)) { g(std::move(termA)); }
}

template <class A, class B, class UnpoolA, class UnpoolB, class Callback>
void Term::unpool(A const &a, B const &b, UnpoolA const &fA, UnpoolB const &fB, Callback const &g) {
    auto poolB(fB(b));
    for (auto &termA : fA(a)) {
        for (auto &termB : poolB) { g(get_clone(termA), get_clone(termB)); }
    }
}

template <class It, class TermUnpool, class Callback>
void Term::unpool(It const &begin, It const &end, TermUnpool const &f, Callback const &g) {
    using R = decltype(f(*begin));
    std::vector<R> pools;
    for (auto it = begin; it != end; ++it) { pools.emplace_back(f(*it)); }
    cross_product(pools);
    for (auto &pooled : pools) { g(std::move(pooled)); }
}

template <class Vec, class TermUnpool>
void Term::unpoolJoin(Vec &vec, TermUnpool const &f) {
    Vec join;
    for (auto &x : vec) {
        auto pool(f(x));
        std::move(pool.begin(), pool.end(), std::back_inserter(join));
    }
    vec = std::move(join);
}

// }}}

} // namespace Gringo

GRINGO_HASH(Gringo::Term)
GRINGO_HASH(Gringo::VarTerm)
GRINGO_HASH(Gringo::GTerm)

#ifdef _MSC_VER
#pragma warning( pop )
#endif

#endif // GRINGO_TERM_HH
