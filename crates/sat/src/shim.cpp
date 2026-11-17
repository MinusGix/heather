// What `src/ffi.rs` calls: one CaDiCaL solver with a proof tracer that
// keeps every derived clause and its antecedents (an LRAT step), in memory.
#include "cadical.hpp"
#include "tracer.hpp"

#include <cstdint>
#include <vector>

namespace {

struct Collector : CaDiCaL::Tracer {
  // Each original clause as: id, length, literals.
  std::vector<int64_t> originals;
  // Each derived clause as: id, length, literals, hint count, hints.
  std::vector<int64_t> steps;
  bool restored = false;

  void add_original_clause (int64_t id, bool, const std::vector<int> &c,
                            bool restore) override {
    if (restore)
      restored = true;
    originals.push_back (id);
    originals.push_back ((int64_t) c.size ());
    for (int l : c)
      originals.push_back (l);
  }

  void add_derived_clause (int64_t id, bool, int, const std::vector<int> &c,
                           const std::vector<int64_t> &chain) override {
    steps.push_back (id);
    steps.push_back ((int64_t) c.size ());
    for (int l : c)
      steps.push_back (l);
    steps.push_back ((int64_t) chain.size ());
    for (int64_t h : chain)
      steps.push_back (h);
  }
};

struct Session {
  CaDiCaL::Solver solver;
  Collector collector;
};

} // namespace

extern "C" {

void *heather_sat_new () {
  Session *s = new Session;
  s->solver.set ("quiet", 1);
  s->solver.set ("lrat", 1);
  s->solver.connect_proof_tracer (&s->collector, true);
  return s;
}

void heather_sat_free (void *p) {
  Session *s = (Session *) p;
  s->solver.disconnect_proof_tracer (&s->collector);
  delete s;
}

void heather_sat_add (void *p, int lit) { ((Session *) p)->solver.add (lit); }

int heather_sat_solve (void *p) { return ((Session *) p)->solver.solve (); }

int heather_sat_val (void *p, int lit) { return ((Session *) p)->solver.val (lit); }

size_t heather_sat_steps_len (void *p) { return ((Session *) p)->collector.steps.size (); }

const int64_t *heather_sat_steps (void *p) { return ((Session *) p)->collector.steps.data (); }

size_t heather_sat_originals_len (void *p) { return ((Session *) p)->collector.originals.size (); }

const int64_t *heather_sat_originals (void *p) { return ((Session *) p)->collector.originals.data (); }

int heather_sat_restored (void *p) { return ((Session *) p)->collector.restored; }

} // extern "C"
