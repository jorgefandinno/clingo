#include <clingo/ground/matcher.hh>
#include <clingo/ground/statement.hh>

#include <clingo/util/print.hh>
#include <clingo/util/unordered_map.hh>

#include <array>
#include <cassert>
#include <ranges>
#include <stdexcept>

namespace CppClingo::Ground {

namespace {

class AssignmentAnalyzer {
  public:
    AssignmentAnalyzer(size_t vars) : vars_{vars} {}
    //! Add an assignment depending on and providing the given variables.
    void add(VariableVec dep, VariableVec prv) {
        std::erase_if(dep, [this](auto var_idx) { return vars_[var_idx].bound; });
        if (dep.empty()) {
            propagate(prv);
        } else {
            vars_[dep.front()].nodes.emplace_back(nodes_.size());
            nodes_.emplace_back(0, std::move(dep), std::move(prv));
        }
    }

    //! Propagate the given variables.
    auto propagate(VariableVec const &vars) -> std::span<size_t const> {
        last_ = trail_.size();
        for (auto var_idx : vars) {
            auto &var = vars_[var_idx];
            if (!var.bound) {
                trail_.emplace_back(var_idx);
                var.bound = true;
            }
        }
        auto extra = trail_.size();
        for (auto cur = last_; cur < trail_.size(); ++cur) {
            auto &var = vars_[trail_[cur]];
            std::erase_if(var.nodes, [&, this](auto node_idx) {
                auto &node = nodes_[node_idx];
                auto dep = node.dep;
                if (auto var_idx = update_(node)) {
                    assert(trail_[cur] != *var_idx);
                    vars_[*var_idx].nodes.emplace_back(node_idx);
                    return true;
                }
                for (auto var_idx : node.prv) {
                    if (!vars_[var_idx].bound) {
                        vars_[var_idx].bound = true;
                        trail_.emplace_back(var_idx);
                    }
                }
                return false;
            });
        }
        return {trail_.begin() + static_cast<std::ptrdiff_t>(extra), trail_.end()};
    }

    //! Undo the last propagate.
    void backtrack() {
        for (auto it = trail_.begin() + static_cast<std::ptrdiff_t>(last_), ie = trail_.end(); it != ie; ++it) {
            vars_[*it].bound = false;
        }
        trail_.resize(last_);
    }

  private:
    struct Var {
        std::vector<size_t> nodes;
        bool bound = false;
    };
    struct Node {
        size_t unbound_;
        VariableVec dep;
        VariableVec prv;
    };

    auto update_(Node &node) -> std::optional<size_t> {
        auto &dep = node.dep;
        for (size_t i = node.unbound_ + 1, e = dep.size(); i < e; ++i) {
            if (!vars_[dep[i]].bound) {
                node.unbound_ = i;
                return dep[i];
            }
        }
        for (size_t i = 0, e = node.unbound_; i < e; ++i) {
            if (!vars_[dep[i]].bound) {
                node.unbound_ = i;
                return dep[i];
            }
        }
        return std::nullopt;
    }

    std::vector<Node> nodes_;
    std::vector<Var> vars_;
    VariableVec trail_;
    size_t last_ = 0;
};


//! A vector of matchers with their depend sets and literal indices in matching order.
using OrderedMatcherVec = std::vector<std::tuple<UMatcher, Instantiator::DependVec, size_t>>;

//! Output recording body literals to output them later.
class LitRecorder : public OutputLit {
  public:
    //! A recorded literal.
    using RecLit = std::tuple<Sign, Symbol, size_t>;

    //! Get the recorded literals.
    [[nodiscard]] auto lits() -> std::vector<RecLit> & { return lits_; }

  private:
    void do_lit(Sign sign, Symbol sym, size_t uid) override { lits_.emplace_back(sign, sym, uid); }
    void do_boolean(bool value) override {
        if (!value) {
            throw std::logic_error("unexpected boolean in decomposed rule");
        }
    }
    auto do_delayed([[maybe_unused]] Sign sign, [[maybe_unused]] std::optional<size_t> uid) -> size_t override {
        throw std::logic_error("unexpected delayed literal in decomposed rule");
    }

    std::vector<RecLit> lits_;
};

//! Decomposes rule bodies at cuts.
//!
//! For each cut, a table maps the values of the separator variables to an
//! entry holding an auxiliary atom. The atom is defined by rules whose bodies
//! consist of the auxiliary atom of the previous cut and the literals between
//! the two cuts. The defining rules are only output once the auxiliary atom is
//! used in the body of another rule. If the body of the first defining rule of
//! an entry consists of facts only, the entry gets no auxiliary atom.
//!
//! Auxiliary atoms have the form `__gringo_projection(<uid>)` so that the text
//! output can be parsed again. Hence, `__gringo_projection/1` is a reserved
//! predicate name.
class RuleDecomposer : public InstanceDecomposer {
  public:
    //! Information about a cut.
    struct Cut {
        //! The separator variables.
        VariableVec sep;
        //! The literals between the previous cut and this cut.
        std::vector<Lit const *> lits;
        //! Whether all literals before the cut are domain literals.
        bool pure;
        //! Whether the table is kept across calls to Instantiator::instantiate.
        bool persistent;
    };

    //! Construct the decomposer for the given cuts and the literals after the last cut.
    RuleDecomposer(std::vector<Cut> cuts, std::vector<Lit const *> lits) : lits_{std::move(lits)} {
        cuts_.reserve(cuts.size());
        for (auto &cut : cuts) {
            cuts_.emplace_back(std::move(cut));
        }
    }

    //! Match the cut with the given index.
    //!
    //! Returns true if the instantiation has to continue after the cut.
    auto next(EvalContext const &ctx, size_t idx) -> bool {
        auto &state = cuts_[idx];
        if (state.cur.has_value()) {
            close_(idx);
            return false;
        }
        auto key = SymbolVec{};
        key.reserve(state.cut.sep.size());
        for (auto var : state.cut.sep) {
            assert(ctx.ass()[var].has_value());
            key.emplace_back(*ctx.ass()[var]);
        }
        if (auto it = state.table.find(key); it != state.table.end()) {
            auto &entry = state.entries[it->second];
            if (entry.status == Status::active && entry.atom.has_value()) {
                activate_(ctx, idx);
                emit_(ctx, define_(ctx, idx, *entry.atom));
            }
            return false;
        }
        auto entry = Entry{};
        if (!state.cut.pure) {
            // If the literals before the cut are facts for this instance, no
            // auxiliary atom is needed (like for pure cuts). Otherwise, it would
            // only be defined by a fact, and the head of the rule could not
            // become a fact.
            if (auto body = define_body_(ctx, idx); !body.empty()) {
                auto uid = ctx.out().uid();
                auto sym = ctx.store().fun_ref(ctx.store().string_ref("__gringo_projection"),
                                               std::array{SymbolStore::num_ref(static_cast<int32_t>(uid))}, false);
                entry.atom = AuxAtom{sym, uid};
                entry.rules.emplace_back(Rule{*entry.atom, std::move(body)});
            }
        }
        state.table.emplace(std::move(key), state.entries.size());
        state.cur = state.entries.size();
        state.entries.emplace_back(std::move(entry));
        return true;
    }

    //! Print the cut with the given index.
    void print(std::ostream &out, size_t idx) const {
        out << "#cut(" << Util::p_range(cuts_[idx].cut.sep, ",", [](std::ostream &out, auto var) {
            out << "X_" << var;
        }) << ")";
    }

  private:
    //! The status of an entry.
    enum class Status : uint8_t {
        pending, //!< The instantiation after the cut has not yet produced an instance.
        active,  //!< The auxiliary atom has been used.
        dead     //!< The instantiation after the cut has not produced an instance.
    };
    //! A rule defining an auxiliary atom.
    struct Rule {
        AuxAtom head;
        std::vector<LitRecorder::RecLit> body;
    };
    //! An entry in the table of a cut.
    struct Entry {
        std::optional<AuxAtom> atom;
        Status status = Status::pending;
        std::vector<Rule> rules;
    };
    //! The state associated with a cut.
    struct State {
        State(Cut cut) : cut{std::move(cut)} {}

        Cut cut;
        Util::unordered_map<SymbolVec, size_t> table;
        std::vector<Entry> entries;
        //! The entry opened by the current visit of the cut.
        std::optional<size_t> cur;
    };

    void do_start() override {
        for (auto &state : cuts_) {
            if (!state.cut.persistent) {
                state.table.clear();
                state.entries.clear();
            }
            state.cur.reset();
        }
    }

    auto do_report(EvalContext const &ctx, InstanceCallback &icb) -> bool override {
        activate_(ctx, cuts_.size());
        auto const &last = cuts_.back();
        assert(last.cur.has_value());
        return icb.report_partial(ctx, lits_, last.entries[*last.cur].atom);
    }

    //! Get the rule defining the given atom for the cut with the given index.
    auto define_(EvalContext const &ctx, size_t idx, AuxAtom const &head) -> Rule {
        return {head, define_body_(ctx, idx)};
    }

    //! Get the body of the rule defining the auxiliary atom for the cut with the given index.
    //!
    //! Literals that are facts are omitted.
    auto define_body_(EvalContext const &ctx, size_t idx) -> std::vector<LitRecorder::RecLit> {
        auto rec = LitRecorder{};
        if (idx > 0) {
            auto const &prev = cuts_[idx - 1];
            assert(prev.cur.has_value());
            if (auto const &atom = prev.entries[*prev.cur].atom; atom.has_value()) {
                rec.lits().emplace_back(Sign::none, atom->first, atom->second);
            }
        }
        for (auto const *lit : cuts_[idx].cut.lits) {
            static_cast<void>(lit->output(ctx, rec));
        }
        return std::move(rec.lits());
    }

    //! Output the given rule.
    static void emit_(EvalContext const &ctx, Rule const &rule) {
        auto &out = ctx.out().body();
        for (auto const &[sign, sym, uid] : rule.body) {
            out.lit(sign, sym, uid);
        }
        ctx.out().rule(std::tuple{rule.head.first, rule.head.second, false});
    }

    //! Output the pending rules of the entries opened by the cuts before the given index.
    void activate_(EvalContext const &ctx, size_t idx) {
        for (size_t i = 0; i < idx; ++i) {
            auto &state = cuts_[i];
            assert(state.cur.has_value());
            auto &entry = state.entries[*state.cur];
            if (entry.status == Status::pending) {
                for (auto const &rule : entry.rules) {
                    emit_(ctx, rule);
                }
                entry.rules.clear();
                entry.status = Status::active;
            }
        }
    }

    //! Close the entry opened by the cut with the given index.
    void close_(size_t idx) {
        auto &state = cuts_[idx];
        auto &entry = state.entries[*state.cur];
        if (entry.status == Status::pending) {
            entry.status = Status::dead;
            entry.rules.clear();
        }
        state.cur.reset();
    }

    std::vector<State> cuts_;
    std::vector<Lit const *> lits_;
};

//! A matcher for a cut in a decomposed rule body.
//!
//! The matcher matches at most once. It fails if the values of the separator
//! variables have been seen before. Backjumping never skips it so that the
//! entry it opened is closed once the instantiation after the cut is complete.
class CutMatcher : public Matcher {
  public:
    //! Construct the matcher for the cut with the given index.
    CutMatcher(RuleDecomposer &dec, size_t idx) : dec_{&dec}, idx_{idx} {}

  private:
    void do_init([[maybe_unused]] InstantiationContext const &ctx, [[maybe_unused]] size_t gen) override {}
    void do_match([[maybe_unused]] EvalContext const &ctx) override {}
    auto do_next(EvalContext const &ctx) -> bool override { return dec_->next(ctx, idx_); }
    void do_print(std::ostream &out) const override { dec_->print(out, idx_); }
    [[nodiscard]] auto do_skippable() const -> bool override { return false; }

    RuleDecomposer *dec_;
    size_t idx_;
};

//! Add the matchers to the instantiator decomposing the body at cuts.
//!
//! A cut is placed before a literal if the literal binds a fresh variable and
//! some variable bound before the literal that was not eliminated at the
//! previous cut does neither occur in the remaining literals nor in the head.
//! Returns false if no cut was found; in this case, the instantiator is left
//! unchanged.
auto add_decomposed(Instantiator &inst, InstanceCallback &cb, OrderedMatcherVec &ordered, VariableSet const &head,
                    std::vector<size_t> const &provided, ULitVec const &lits) -> bool {
    auto n = ordered.size();
    auto lit_at = [&](size_t k) -> Lit const & { return *lits[std::get<2>(ordered[k])]; };
    // gather variables of literals and of suffixes
    auto vars = std::vector<VariableSet>(n);
    for (size_t k = 0; k < n; ++k) {
        lit_at(k).vars(vars[k], VarSelectMode::all);
    }
    auto later = std::vector<VariableSet>(n + 1);
    for (size_t k = n; k-- > 0;) {
        later[k] = later[k + 1];
        later[k].insert(vars[k].begin(), vars[k].end());
    }
    // compute cut positions and separators
    auto pos = std::vector<size_t>{};
    auto seps = std::vector<VariableVec>{};
    auto bound = VariableSet{};
    size_t num_elim = 0;
    for (size_t k = 0; k < n; ++k) {
        if (k > 0 && !std::ranges::all_of(vars[k], [&](auto var) { return bound.contains(var); })) {
            auto sep = VariableVec{};
            size_t elim = 0;
            for (auto var : bound) {
                if (later[k].contains(var) || head.contains(var)) {
                    sep.emplace_back(var);
                } else {
                    ++elim;
                }
            }
            if (elim != num_elim) {
                std::ranges::sort(sep);
                pos.emplace_back(k);
                seps.emplace_back(std::move(sep));
                num_elim = elim;
            }
        }
        bound.insert(vars[k].begin(), vars[k].end());
    }
    if (pos.empty()) {
        return false;
    }
    auto num_cuts = pos.size();
    // map old matcher indices to new ones taking cut matchers into account
    auto index = std::vector<size_t>(n);
    for (size_t k = 0, c = 0; k < n; ++k) {
        while (c < num_cuts && pos[c] <= k) {
            ++c;
        }
        index[k] = k + c;
    }
    auto prov = [&](VariableSet const &select) {
        auto res = Instantiator::DependVec{};
        for (auto var : select) {
            res.emplace_back(index[provided[var]]);
        }
        std::ranges::sort(res);
        res.erase(std::ranges::unique(res).begin(), res.end());
        return res;
    };
    // gather the literals and the important variables of a block of literals
    auto block_lits = [&](size_t begin, size_t end) {
        auto idx = std::vector<size_t>{};
        for (size_t k = begin; k < end; ++k) {
            idx.emplace_back(std::get<2>(ordered[k]));
        }
        std::ranges::sort(idx);
        auto res = std::vector<Lit const *>{};
        for (auto i : idx) {
            res.emplace_back(lits[i].get());
        }
        return res;
    };
    auto block_important = [&](size_t begin, size_t end, VariableSet &res) {
        for (size_t k = begin; k < end; ++k) {
            if (cb.is_important(std::get<2>(ordered[k])) && !lit_at(k).domain()) {
                res.insert(vars[k].begin(), vars[k].end());
            }
        }
    };
    // create the decomposer
    auto cuts = std::vector<RuleDecomposer::Cut>{};
    auto cut_depends = std::vector<Instantiator::DependVec>{};
    for (size_t c = 0; c < num_cuts; ++c) {
        auto begin = c > 0 ? pos[c - 1] : 0;
        auto dep = VariableSet{seps[c].begin(), seps[c].end()};
        block_important(begin, pos[c], dep);
        if (c > 0) {
            dep.insert(seps[c - 1].begin(), seps[c - 1].end());
        }
        cut_depends.emplace_back(prov(dep));
        auto pure = true;
        for (size_t k = 0; k < pos[c]; ++k) {
            pure = pure && lit_at(k).domain();
        }
        auto persistent = true;
        for (size_t k = pos[c]; k < n; ++k) {
            persistent = persistent && lit_at(k).single_pass();
        }
        cuts.emplace_back(seps[c], block_lits(begin, pos[c]), pure, persistent);
    }
    auto dec = std::make_unique<RuleDecomposer>(std::move(cuts), block_lits(pos.back(), n));
    // add the matchers
    for (size_t k = 0, c = 0; k < n; ++k) {
        for (; c < num_cuts && pos[c] == k; ++c) {
            inst.add(std::make_unique<CutMatcher>(*dec, c), cut_depends[c]);
        }
        auto &[matcher, depend, lit_idx] = ordered[k];
        for (auto &d : depend) {
            d = index[d];
        }
        inst.add(std::move(matcher), std::move(depend));
    }
    auto solution = VariableSet{head.begin(), head.end()};
    block_important(pos.back(), n, solution);
    solution.insert(seps.back().begin(), seps.back().end());
    inst.finalize(prov(solution));
    inst.decompose(std::move(dec));
    return true;
}

} // namespace

void Linearizer::start(Queue &queue) {
    iqueue_ = &queue;
}

void Linearizer::prepare(InstanceCallback &cb, ULitVec const &body, VariableSet important) {
    auto head = important;
    auto decompose = decompose_ && cb.decomposable() &&
                     std::ranges::all_of(body, [](auto const &lit) { return lit->decomposable(); });
    rec_.clear();
    todos_.clear();
    todos_.emplace_back();
    auto i = size_t{0};
    // gather indices of recursive literals and extend important variables
    for (auto const &lit : body) {
        todos_.back().emplace_back(MatcherType::all_atoms);
        if (!lit->single_pass()) {
            rec_.emplace_back(i);
        }
        if (cb.is_important(i) && !lit->domain()) {
            lit->vars(important, VarSelectMode::all);
        }
        ++i;
    }
    // compute linearization
    todos_.reserve(rec_.size());
    for (auto i : rec_) {
        todos_.back()[i] = MatcherType::new_atoms;
        if (i != rec_.back()) {
            todos_.emplace_back(todos_.back());
            todos_.back()[i] = MatcherType::old_atoms;
        }
    }
    build_(body);
    for (auto const &todo : todos_) {
        auto [inst, index] = order_(cb, todo, important, head, decompose, body);
        iqueue_->insert(std::move(inst), index);
    }
}

void Linearizer::build_(ULitVec const &lits) {
    lit_map_.clear();
    var_map_.clear();
    auto i = size_t{0};
    auto vars = VariableSet{};
    auto num_vars = size_t{0};
    lit_map_.reserve(lits.size());
    for (auto const &lit : lits) {
        lit->vars(vars, VarSelectMode::depend);
        auto dep = std::vector<size_t>(vars.begin(), vars.end());
        vars.clear();
        lit->vars(vars, VarSelectMode::provide);
        auto prv = std::vector<size_t>(vars.begin(), vars.end());
        vars.clear();
        num_vars = std::accumulate(dep.begin(), dep.end(), num_vars, [](auto a, auto b) { return std::max(a, b + 1); });
        num_vars = std::accumulate(prv.begin(), prv.end(), num_vars, [](auto a, auto b) { return std::max(a, b + 1); });
        lit_map_.emplace_back(0, std::move(dep), std::move(prv));
        ++i;
    }
    i = 0;
    var_map_.resize(num_vars);
    for (auto const &ndp : lit_map_) {
        for (auto var : std::get<1>(ndp)) {
            var_map_[var].emplace_back(i);
        }
        ++i;
    }
}

auto Linearizer::order_(InstanceCallback &cb, std::vector<MatcherType> const &todo, VariableSet const &important,
                        VariableSet const &head, bool decompose, ULitVec const &lits)
    -> std::pair<Instantiator, std::optional<size_t>> {
    auto inst = Instantiator{cb, var_map_.size(), lits.size()};
    size_t gen = 0;
    queue_.clear();
    auto i = size_t{0};
    // initialize the queue
    for (auto &[cur, dep, prv] : lit_map_) {
        if (cur = dep.size(); cur == 0) {
            queue_.emplace_back(i, ++gen, 0);
        }
        ++i;
    }
    auto provided = std::vector<size_t>(var_map_.size(), 0);
    auto bound = std::vector<bool>(var_map_.size(), false);
    auto make_depend = [&provided, &bound](auto const &dep, auto const &prv) {
        auto res = std::vector<size_t>{};
        for (auto var : dep) {
            assert(var < provided.size());
            res.emplace_back(provided[var]);
        }
        for (auto var : prv) {
            if (bound[var]) {
                res.emplace_back(provided[var]);
            }
        }
        std::ranges::sort(res);
        res.erase(std::ranges::unique(res).begin(), res.end());
        return res;
    };
    // process the queue
    auto ordered = OrderedMatcherVec{};
    ordered.reserve(lits.size());
    auto done = Util::unordered_set<Lit const *>{};
    done.reserve(lits.size());
    auto res_index = std::optional<size_t>{};
    // initialize the analyzer
    auto analyzer = AssignmentAnalyzer{var_map_.size()};
    for (size_t k = 0, n = lits.size(); k < n; ++k) {
        auto const &[cur, dep, prv] = lit_map_[k];
        if (!dep.empty()) {
            // Note: variables are deliberately swapped, see (*)
            analyzer.add(prv, dep);
        }
    }
    // Estimate not-yet-grounded recursive domains at the largest known domain size in the body, so a
    // size-0 recursive literal is not mistaken for a trivially cheap one when ordering.
    double estimate = 0;
    size_t num_selected = 0;

    for (auto const &lit : lits) {
        // TODO: it is also possible to combine the score and domain_size functions
        if (auto size = lit->domain_size(sel_)) {
            if (*size <= 0) {
                continue;
            }
            ++num_selected;
            if (fun_ == EstimateFunction::maximum) {
                estimate = std::max(estimate, *size);
            } else if (fun_ == EstimateFunction::minimum) {
                estimate = std::min(estimate, *size);
            } else if (fun_ == EstimateFunction::average) {
                estimate += *size;
            }
        }
    }
    if (num_selected == 0) {
        // We set the estimate to a large fixed value to at least exploit some
        // structural information among the literals.
        estimate = default_estimate_size;
    } else if (fun_ == EstimateFunction::average) {
        estimate /= static_cast<double>(num_selected);
    }
    for (size_t k = 0; !queue_.empty();) {
        // recompute score
        for (auto &[idx, gen, score] : queue_) {
            score = -1;
            // compute the assignments propagated by this choice of literal
            auto const &[cur, dep, prv] = lit_map_[idx];
            if (!std::ranges::all_of(prv, [&bound](auto idx) { return bound[idx]; })) {
                score = lits[idx]->score(bound, estimate);
                if (score > 0) {
                    auto extra = analyzer.propagate(prv);
                    if (!extra.empty()) {
                        // (*) each variable that is provided by an assignment increases the score
                        score *= 1.0 + static_cast<double>(extra.size());
                    }
                    analyzer.backtrack();
                }
            }
        }
        // get minimum element in queue (breaking ties using insertion order)
        auto pred = [&](auto const &ei, auto const &ej) -> bool {
            auto si = get<2>(ei);
            auto sj = get<2>(ej);
            auto ti = todo[get<0>(ei)];
            auto tj = todo[get<0>(ej)];
            if ((ti == MatcherType::new_atoms || tj == MatcherType::new_atoms) && (si >= 0 && sj >= 0)) {
                assert(ti != tj);
                return ti < tj;
            }
            return std::tie(si, get<1>(ei)) < std::tie(sj, get<1>(ej));
        };
        std::iter_swap(queue_.rbegin(), std::ranges::min_element(std::ranges::reverse_view(queue_), pred));
        i = get<0>(queue_.back());
        queue_.pop_back();
        // skip if an equivalent matcher has already been added (i.e., X=Y and Y=X)
        if (!done.emplace(lits[i].get()).second && todo[i] == MatcherType::all_atoms) {
            // the decomposition requires a matcher for each literal
            decompose = false;
            continue;
        }
        auto [matcher, index] = lits[i]->matcher(*mbr_, todo[i], bound);
        if (index) {
            res_index = index;
        }
        auto const &[cur, dep, prv] = lit_map_[i];
        ordered.emplace_back(std::move(matcher), make_depend(dep, prv), i);
        for (auto var : prv) {
            if (bound[var]) {
                continue;
            }
            assert(var < var_map_.size());
            for (auto j : var_map_[var]) {
                if (--std::get<0>(lit_map_[j]) == 0) {
                    queue_.emplace_back(j, ++gen, 0);
                }
            }
            provided[var] = k;
            bound[var] = true;
        }
        ++k;
    }
    if (!decompose || !add_decomposed(inst, cb, ordered, head, provided, lits)) {
        for (auto &[matcher, depend, lit_idx] : ordered) {
            inst.add(std::move(matcher), std::move(depend));
        }
        inst.finalize(make_depend(important, std::vector<size_t>{}));
    }
    return {std::move(inst), res_index};
}

void StmRule::init_() {
    if (head_) {
        body_.emplace_back(std::make_unique<LitFactCheck>(*base_, *head_, atom_));
    }
}

void StmRule::do_print_head(std::ostream &out) const {
    if (head_) {
        if (type_ == RuleType::choice) {
            out << "{ " << *head_ << " }";
        } else {
            out << *head_;
        }
    }
}

void StmRule::do_print(std::ostream &out) const {
    out << "max: ";
    print_head(out);
    if (!indices_.empty()) {
        out << "[" << Util::p_range(indices_, ",") << "]";
    }
    out << " :- " << Util::p_range(body_, ", ", [](std::ostream &out, auto const &lit) { out << *lit; }) << ".";
}

auto StmRule::do_body() const -> ULitVec const & {
    return body_;
}

auto StmRule::do_important() const -> VariableSet {
    VariableSet important;
    if (head_) {
        head_->vars(important);
    }
    return important;
}

void StmRule::do_init(size_t gen) {
    if (base_ != nullptr) {
        base_->update(gen);
    }
}

auto StmRule::do_report(EvalContext const &ctx) -> bool {
    bool fact = type_ == RuleType::normal;
    auto &out = ctx.out().body();
    for (auto const &lit : body_) {
        if (lit->output(ctx, out)) {
            fact = false;
        }
    }
    return report_head_(ctx, fact);
}

auto StmRule::do_report_partial(EvalContext const &ctx, std::span<Lit const *const> lits, std::optional<AuxAtom> aux)
    -> bool {
    bool fact = type_ == RuleType::normal;
    auto &out = ctx.out().body();
    if (aux.has_value()) {
        out.lit(Sign::none, aux->first, aux->second);
        fact = false;
    }
    for (auto const *lit : lits) {
        if (lit->output(ctx, out)) {
            fact = false;
        }
    }
    return report_head_(ctx, fact);
}

auto StmRule::report_head_(EvalContext const &ctx, bool fact) -> bool {
    if (head_ != nullptr) {
        auto it = base_
                      ->add(atom_, fact ? StateAtom::fact : StateAtom::derived,
                            [&ctx, fact]() { return ctx.out().uid(fact); })
                      .first;
        ctx.out().rule(std::tuple{atom_, static_cast<size_t>(it.value().id), type_ == RuleType::choice});
    } else if (type_ == RuleType::normal) {
        ctx.out().rule(std::nullopt);
    }
    return head_ != nullptr || !fact;
}

void StmRule::do_propagate([[maybe_unused]] SymbolStore &store, [[maybe_unused]] OutputStm &out, Queue &queue) {
    // Consider adding the propagation to the instantiator...
    if (base_ != nullptr && base_->has_update()) {
        for (auto const &idx : indices_) {
            queue.propagate(idx);
        }
    }
}

// definition of StmExternal

void StmExternal::init_() {
    class LitExternalCheck : public LitCheck {
      public:
        LitExternalCheck(StmExternal &stm) : stm_{&stm} {}

      private:
        [[nodiscard]] auto do_check(EvalContext const &ctx) -> bool override {
            if (auto atom = stm_->atom_->eval(ctx); atom && !stm_->base_->is_fact(*atom)) {
                stm_->res_atom_ = *atom;
            } else {
                return false;
            }
            if (stm_->type_) {
                if (auto type = stm_->type_->second->eval(ctx); type && type->type() == SymbolType::function &&
                                                                type->args().empty() && !type->has_classical_sign()) {
                    if (type->name() == "true") {
                        stm_->res_type_ = ExternalType::true_;
                    } else if (type->name() == "false") {
                        stm_->res_type_ = ExternalType::false_;
                    } else if (type->name() == "free") {
                        stm_->res_type_ = ExternalType::free;
                    } else if (type->name() == "release") {
                        stm_->res_type_ = ExternalType::release;
                    } else {
                        return expect(ctx, stm_->type_->first, logged_, "unexpected external type (got ", *type, ")");
                    }
                } else {
                    return false;
                }
            } else {
                stm_->res_type_ = ExternalType::false_;
            }
            return true;
        }
        void do_vars(VariableSet &vars, VarSelectMode mode) const override {
            if (mode != VarSelectMode::provide) {
                if (stm_->type_) {
                    stm_->type_->second->vars(vars);
                }
                stm_->atom_->vars(vars);
            }
        }
        void do_print(std::ostream &out) const override {
            out << "#check(" << *stm_->atom_;
            if (stm_->type_) {
                out << "," << *stm_->type_->second;
            }
            out << ")";
        }
        [[nodiscard]] auto do_copy() const -> ULit override { return std::make_unique<LitExternalCheck>(*stm_); }

        StmExternal *stm_;
        bool logged_ = false;
    };
    body_.emplace_back(std::make_unique<LitExternalCheck>(*this));
}

void StmExternal::do_print_head(std::ostream &out) const {
    out << "#external " << *atom_;
}

void StmExternal::do_print(std::ostream &out) const {
    out << "max: ";
    print_head(out);
    if (!indices_.empty()) {
        out << "[" << Util::p_range(indices_, ",") << "]";
    }
    out << " :- " << Util::p_range(body_, ", ", [](std::ostream &out, auto const &lit) { out << *lit; }) << ".";
    if (type_) {
        out << " [" << *type_->second << "]";
    }
}

auto StmExternal::do_body() const -> ULitVec const & {
    return body_;
}

auto StmExternal::do_important() const -> VariableSet {
    VariableSet important;
    atom_->vars(important);
    if (type_) {
        type_->second->vars(important);
    }
    return important;
}

void StmExternal::do_init(size_t gen) {
    base_->update(gen);
}

auto StmExternal::do_report(EvalContext const &ctx) -> bool {
    auto it = base_->add(res_atom_, StateAtom::derived, [&ctx]() { return ctx.out().uid(); }).first;
    ctx.out().external(res_atom_, it.value().id, res_type_);
    return true;
}

void StmExternal::do_propagate([[maybe_unused]] SymbolStore &store, [[maybe_unused]] OutputStm &out, Queue &queue) {
    // Consider adding the propagation to the instantiator...
    if (base_->has_update()) {
        for (auto const &idx : indices_) {
            queue.propagate(idx);
        }
    }
}

// definition of StmWeakConstraint

void StmWeakConstraint::init_() {
    class LitTupleCheck : public LitCheck {
      public:
        LitTupleCheck(StmWeakConstraint &stm) : stm_{&stm} {}

      private:
        [[nodiscard]] auto do_check(EvalContext const &ctx) -> bool override {
            if (auto weight = stm_->weight_->eval(ctx);
                weight && (weight->type() == SymbolType::number ||
                           expect(ctx, stm_->loc_weight_, logged_, "number expected (", *weight, ")"))) {
                stm_->res_weight_ = *weight;
            } else {
                return false;
            }
            if (stm_->prio_) {
                if (auto prio = stm_->prio_->eval(ctx);
                    prio && (prio->type() == SymbolType::number ||
                             expect(ctx, stm_->loc_prio_, logged_, "number expected (", *prio, ")"))) {
                    stm_->res_prio_ = *prio;
                } else {
                    return false;
                }
            } else {
                stm_->res_prio_ = std::nullopt;
            }
            stm_->res_terms_.clear();
            for (auto const &term : stm_->terms_) {
                if (auto sym = term->eval(ctx)) {
                    stm_->res_terms_.emplace_back(*sym);
                } else {
                    return false;
                }
            }
            return true;
        }
        void do_vars(VariableSet &vars, VarSelectMode mode) const override {
            if (mode != VarSelectMode::provide) {
                stm_->weight_->vars(vars);
                if (stm_->prio_) {
                    stm_->prio_->vars(vars);
                }
                for (auto const &term : stm_->terms_) {
                    term->vars(vars);
                }
            }
        }
        void do_print(std::ostream &out) const override {
            out << "#check(" << *stm_->weight_;
            if (stm_->prio_) {
                out << "@" << *stm_->prio_;
            }
            for (auto const &term : stm_->terms_) {
                out << "," << *term;
            }
            out << ")";
        }
        [[nodiscard]] auto do_copy() const -> ULit override { return std::make_unique<LitTupleCheck>(*stm_); }

        StmWeakConstraint *stm_;
        bool logged_ = false;
    };
    res_terms_.reserve(terms_.size());
    body_.emplace_back(std::make_unique<LitTupleCheck>(*this));
}

void StmWeakConstraint::do_print(std::ostream &out) const {
    out << "max: ";
    out << " :~ " << Util::p_range(body_, ", ", [](std::ostream &out, auto const &lit) { out << *lit; }) << ". ";
    print_head(out);
}

auto StmWeakConstraint::do_body() const -> ULitVec const & {
    return body_;
}

auto StmWeakConstraint::do_important() const -> VariableSet {
    VariableSet vars;
    weight_->vars(vars);
    if (prio_) {
        prio_->vars(vars);
    }
    for (auto const &term : terms_) {
        term->vars(vars);
    }
    return vars;
}

void StmWeakConstraint::do_print_head(std::ostream &out) const {
    out << "[" << *weight_;
    if (prio_) {
        out << "@" << *prio_;
    }
    for (auto const &term : terms_) {
        out << "," << *term;
    }
    out << "]";
}

void StmWeakConstraint::do_init([[maybe_unused]] size_t gen) {
}

auto StmWeakConstraint::do_report(EvalContext const &ctx) -> bool {
    auto &out = ctx.out().body();
    for (auto const &lit : body_) {
        std::ignore = lit->output(ctx, out);
    }
    ctx.out().weak_constraint(res_weight_.num(), res_prio_ ? &res_prio_->num() : nullptr, res_terms_);
    return true;
}

void StmWeakConstraint::do_propagate([[maybe_unused]] SymbolStore &store, [[maybe_unused]] OutputStm &out,
                                     [[maybe_unused]] Queue &queue) {
}

// definitition of StmHeuristic

void StmHeuristic::init_() {
    class LitHeuristicCheck : public LitCheck {
      public:
        LitHeuristicCheck(StmHeuristic &stm) : stm_{&stm} {}

      private:
        [[nodiscard]] auto do_check(EvalContext const &ctx) -> bool override {
            if (auto weight = stm_->weight_->eval(ctx);
                weight && (weight->type() == SymbolType::number ||
                           expect(ctx, stm_->loc_weight_, logged_, "number expected (got ", *weight, ")"))) {
                stm_->res_weight_ = *weight;
            } else {
                return false;
            }
            if (stm_->prio_) {
                if (auto prio = stm_->prio_->eval(ctx);
                    prio && (prio->type() == SymbolType::number ||
                             expect(ctx, stm_->loc_prio_, logged_, "number expected (got ", *prio, ")"))) {
                    stm_->res_prio_ = *prio;
                } else {
                    return false;
                }
            }
            if (auto type = stm_->type_->eval(ctx);
                type && type->type() == SymbolType::function && type->args().empty() && !type->has_classical_sign()) {
                if (type->name() == "factor") {
                    stm_->res_type_ = HeuristicType::factor;
                } else if (type->name() == "false") {
                    stm_->res_type_ = HeuristicType::false_;
                } else if (type->name() == "init") {
                    stm_->res_type_ = HeuristicType::init;
                } else if (type->name() == "level") {
                    stm_->res_type_ = HeuristicType::level;
                } else if (type->name() == "sign") {
                    stm_->res_type_ = HeuristicType::sign;
                } else if (type->name() == "true") {
                    stm_->res_type_ = HeuristicType::true_;
                } else {
                    return expect(ctx, stm_->loc_type_, logged_, "unexpected heuristic modifier (got ", *type, ")");
                }
            } else {
                return false;
            }
            return true;
        }
        void do_vars(VariableSet &vars, VarSelectMode mode) const override {
            if (mode != VarSelectMode::provide) {
                stm_->weight_->vars(vars);
                if (stm_->prio_) {
                    stm_->prio_->vars(vars);
                }
                stm_->type_->vars(vars);
            }
        }
        void do_print(std::ostream &out) const override {
            out << "#check(" << *stm_->weight_;
            if (stm_->prio_) {
                out << "," << *stm_->prio_;
            }
            out << "," << *stm_->type_ << ")";
        }
        [[nodiscard]] auto do_copy() const -> ULit override { return std::make_unique<LitHeuristicCheck>(*stm_); }

        StmHeuristic *stm_;
        bool logged_ = false;
    };

    class LitAtom : public Lit {
      public:
        LitAtom(StmHeuristic &stm) : stm_{&stm} {}

      private:
        void do_print(std::ostream &out) const override { out << *stm_->atom_; }

        [[nodiscard]] auto do_output([[maybe_unused]] EvalContext const &ctx, [[maybe_unused]] OutputLit &out) const
            -> bool override {
            return false;
        }

        [[nodiscard]] auto do_copy() const -> ULit override { return std::make_unique<LitAtom>(*stm_); }

        [[nodiscard]] auto do_domain() const -> bool override { return true; }

        [[nodiscard]] auto do_single_pass() const -> bool override { return true; }

        void do_vars(VariableSet &vars, VarSelectMode mode) const override {
            if (mode != VarSelectMode::depend) {
                stm_->atom_->vars(vars);
            }
        }

        [[nodiscard]] auto do_matcher(std::pmr::monotonic_buffer_resource &mbr, MatcherType type,
                                      std::vector<bool> const &bound)
            -> std::pair<UMatcher, std::optional<size_t>> override {
            return {make_atom_matcher(mbr, bound, *stm_->base_, *stm_->atom_, type, stm_->offset_), std::nullopt};
        }

        [[nodiscard]] auto do_score(std::vector<bool> const &bound, [[maybe_unused]] double estimate) const
            -> double override {
            return stm_->atom_->score(static_cast<double>(stm_->base_->size()), bound);
        }

        [[nodiscard]] auto do_domain_size([[maybe_unused]] EstimateSelector sel) const
            -> std::optional<double> override {
            return stm_->base_->size();
        }

        [[nodiscard]] auto do_hash() const -> size_t override { return std::hash<LitAtom const *>{}(this); }

        [[nodiscard]] auto do_equal_to(Lit const &other) const -> bool override { return this == &other; }

        [[nodiscard]] auto do_compare_to(Lit const &other) const -> std::weak_ordering override {
            return this <=> &other;
        }

        StmHeuristic *stm_;
    };
    body_.emplace_back(std::make_unique<LitAtom>(*this));
    body_.emplace_back(std::make_unique<LitHeuristicCheck>(*this));
}

void StmHeuristic::do_print(std::ostream &out) const {
    out << "max: ";
    print_head(out);
    out << " :- " << Util::p_range(body_, ", ", [](std::ostream &out, auto const &lit) { out << *lit; }) << ".";
}

auto StmHeuristic::do_body() const -> ULitVec const & {
    return body_;
}

auto StmHeuristic::do_important() const -> VariableSet {
    VariableSet vars;
    atom_->vars(vars);
    weight_->vars(vars);
    if (prio_) {
        prio_->vars(vars);
    }
    type_->vars(vars);
    return vars;
}

void StmHeuristic::do_print_head(std::ostream &out) const {
    out << "#heuristic " << *atom_ << " [" << *weight_;
    if (prio_) {
        out << "@" << *prio_;
    }
    out << "," << *type_ << "]";
}

void StmHeuristic::do_init([[maybe_unused]] size_t gen) {
}

auto StmHeuristic::do_report(EvalContext const &ctx) -> bool {
    auto &out = ctx.out().body();
    for (auto const &lit : body_) {
        std::ignore = lit->output(ctx, out);
    }
    auto atom = base_->nth(offset_);
    ctx.out().heuristic(atom.key(), atom.value().id, res_weight_.num(), prio_ ? &res_prio_.num() : nullptr, res_type_);
    return true;
}

void StmHeuristic::do_propagate([[maybe_unused]] SymbolStore &store, [[maybe_unused]] OutputStm &out,
                                [[maybe_unused]] Queue &queue) {
}

// definitition of StmEdge

void StmEdge::init_() {
    class LitEdgeCheck : public LitCheck {
      public:
        LitEdgeCheck(StmEdge &stm) : stm_{&stm} {}

      private:
        [[nodiscard]] auto do_check(EvalContext const &ctx) -> bool override {
            if (auto src = stm_->src_->eval(ctx)) {
                stm_->res_src_ = *src;
            } else {
                return false;
            }
            if (auto dst = stm_->dst_->eval(ctx)) {
                stm_->res_dst_ = *dst;
            } else {
                return false;
            }
            return true;
        }
        void do_vars(VariableSet &vars, VarSelectMode mode) const override {
            if (mode != VarSelectMode::provide) {
                stm_->src_->vars(vars);
                stm_->dst_->vars(vars);
            }
        }
        void do_print(std::ostream &out) const override {
            out << "#check(" << *stm_->src_;
            out << "," << *stm_->dst_ << ")";
        }
        [[nodiscard]] auto do_copy() const -> ULit override { return std::make_unique<LitEdgeCheck>(*stm_); }

        StmEdge *stm_;
    };
    body_.emplace_back(std::make_unique<LitEdgeCheck>(*this));
}

void StmEdge::do_print(std::ostream &out) const {
    out << "max: ";
    print_head(out);
    out << " :- " << Util::p_range(body_, ", ", [](std::ostream &out, auto const &lit) { out << *lit; }) << ".";
}

auto StmEdge::do_body() const -> ULitVec const & {
    return body_;
}

auto StmEdge::do_important() const -> VariableSet {
    VariableSet vars;
    src_->vars(vars);
    dst_->vars(vars);
    return vars;
}

void StmEdge::do_print_head(std::ostream &out) const {
    out << "#edge (" << *src_ << "," << *dst_ << ")";
}

void StmEdge::do_init([[maybe_unused]] size_t gen) {
}

auto StmEdge::do_report(EvalContext const &ctx) -> bool {
    auto &out = ctx.out().body();
    for (auto const &lit : body_) {
        std::ignore = lit->output(ctx, out);
    }
    ctx.out().edge(res_src_, res_dst_);
    return true;
}

void StmEdge::do_propagate([[maybe_unused]] SymbolStore &store, [[maybe_unused]] OutputStm &out,
                           [[maybe_unused]] Queue &queue) {
}

// definitition of StmShow

void StmShow::init_() {
    class LitShowCheck : public LitCheck {
      public:
        LitShowCheck(StmShow &stm) : stm_{&stm} {}

      private:
        [[nodiscard]] auto do_check(EvalContext const &ctx) -> bool override {
            if (auto term = stm_->term_->eval(ctx)) {
                stm_->res_term_ = *term;
                return true;
            }
            return false;
        }
        void do_vars(VariableSet &vars, VarSelectMode mode) const override {
            if (mode != VarSelectMode::provide) {
                stm_->term_->vars(vars);
            }
        }
        void do_print(std::ostream &out) const override { out << "#check(" << *stm_->term_ << ")"; }
        [[nodiscard]] auto do_copy() const -> ULit override { return std::make_unique<LitShowCheck>(*stm_); }

        StmShow *stm_;
    };
    body_.emplace_back(std::make_unique<LitShowCheck>(*this));
}

void StmShow::do_print(std::ostream &out) const {
    out << "max: ";
    print_head(out);
    out << " :- " << Util::p_range(body_, ", ", [](std::ostream &out, auto const &lit) { out << *lit; }) << ".";
}

auto StmShow::do_body() const -> ULitVec const & {
    return body_;
}

auto StmShow::do_important() const -> VariableSet {
    VariableSet vars;
    term_->vars(vars);
    return vars;
}

void StmShow::do_print_head(std::ostream &out) const {
    out << "#show " << *term_;
}

void StmShow::do_init([[maybe_unused]] size_t gen) {
}

auto StmShow::do_report(EvalContext const &ctx) -> bool {
    auto &out = ctx.out().body();
    for (auto const &lit : body_) {
        std::ignore = lit->output(ctx, out);
    }
    ctx.out().show_term(res_term_);
    return true;
}

void StmShow::do_propagate([[maybe_unused]] SymbolStore &store, [[maybe_unused]] OutputStm &out,
                           [[maybe_unused]] Queue &queue) {
}

// definitition of StmProject

void StmProject::init_() {
    class LitProject : public Lit {
      public:
        LitProject(StmProject &stm) : stm_{&stm} {}

      private:
        void do_print(std::ostream &out) const override { out << *stm_->atom_; }

        [[nodiscard]] auto do_output([[maybe_unused]] EvalContext const &ctx, [[maybe_unused]] OutputLit &out) const
            -> bool override {
            return false;
        }

        [[nodiscard]] auto do_copy() const -> ULit override { return std::make_unique<LitProject>(*stm_); }

        [[nodiscard]] auto do_domain() const -> bool override { return true; }

        [[nodiscard]] auto do_single_pass() const -> bool override { return true; }

        void do_vars(VariableSet &vars, VarSelectMode mode) const override {
            if (mode != VarSelectMode::depend) {
                stm_->atom_->vars(vars);
            }
        }

        [[nodiscard]] auto do_matcher(std::pmr::monotonic_buffer_resource &mbr, MatcherType type,
                                      std::vector<bool> const &bound)
            -> std::pair<UMatcher, std::optional<size_t>> override {
            return {make_atom_matcher(mbr, bound, *stm_->base_, *stm_->atom_, type, stm_->offset_), std::nullopt};
        }

        [[nodiscard]] auto do_score(std::vector<bool> const &bound, [[maybe_unused]] double estimate) const
            -> double override {
            return stm_->atom_->score(static_cast<double>(stm_->base_->size()), bound);
        }

        [[nodiscard]] auto do_domain_size([[maybe_unused]] EstimateSelector sel) const
            -> std::optional<double> override {
            return stm_->base_->size();
        }

        [[nodiscard]] auto do_hash() const -> size_t override { return std::hash<LitProject const *>{}(this); }

        [[nodiscard]] auto do_equal_to(Lit const &other) const -> bool override { return this == &other; }

        [[nodiscard]] auto do_compare_to(Lit const &other) const -> std::weak_ordering override {
            return this <=> &other;
        }

        StmProject *stm_;
    };
    body_.emplace_back(std::make_unique<LitProject>(*this));
}

void StmProject::do_print(std::ostream &out) const {
    out << "max: ";
    print_head(out);
    out << " :- " << Util::p_range(body_, ", ", [](std::ostream &out, auto const &lit) { out << *lit; }) << ".";
}

auto StmProject::do_body() const -> ULitVec const & {
    return body_;
}

auto StmProject::do_important() const -> VariableSet {
    VariableSet vars;
    atom_->vars(vars);
    return vars;
}

void StmProject::do_print_head(std::ostream &out) const {
    out << "#project " << *atom_;
}

void StmProject::do_init([[maybe_unused]] size_t gen) {
}

auto StmProject::do_report(EvalContext const &ctx) -> bool {
    auto atom = base_->nth(offset_);
    ctx.out().project(atom.key(), atom.value().id);
    return true;
}

void StmProject::do_propagate([[maybe_unused]] SymbolStore &store, [[maybe_unused]] OutputStm &out,
                              [[maybe_unused]] Queue &queue) {
}

} // namespace CppClingo::Ground
