/*++
  Module Name:

  spacer_adhoc_generalizer.cpp

  Abstract:

  Adhoc lemma generalizer (based on quant_gen).

  Author:

  Jeff

  Revision History:

  --*/


#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_sem_matcher.h"
#include "muz/spacer/spacer_antiunify.h"
#include "ast/substitution/substitution.h"

#include "ast/ast_util.h"
#include "ast/expr_abstract.h"
#include "ast/rewriter/var_subst.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/factor_equivs.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/substitution/matcher.h"
#include "ast/expr_functors.h"


using namespace spacer;

namespace spacer {

  lemma_adhoc_generalizer::lemma_adhoc_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m) {}

void lemma_adhoc_generalizer::operator()(lemma_ref &lemma){
  TRACE("spacer_adhoc_genz",
    tout << "Initial cube: " << mk_and(lemma->get_cube()) << "\n";);

  pred_transformer &pt = lemma->get_pob()->pt();
  pob *p = &*lemma->get_pob();

  // parent-matching
  unsigned i = 0;
  sem_matcher smatcher(m);
  anti_unifier antiU(m);
  substitution subs1(m), subs2(m);
  expr_ref result(m), result_buffer(m);
  result_buffer = mk_and(lemma->get_cube());   // XXX use TRUE instead
  bool pos = false;
  TRACE("adhoc_parent_matching",
        tout << "Initial cube:" << mk_and(lemma->get_cube()) << "\n" ;);
  while(p->parent()){

    i = 0;
    p = p->parent();

    for(auto &lms:p->lemmas()){
      TRACE("adhoc_parent_matching", tout << "Parent_" << i++ << ": "<< mk_and(lms->get_cube()) << "\n";);
      antiU( mk_and(lemma->get_cube()), mk_and(lms->get_cube()), result, subs1, subs2);
      TRACE("adhoc_parent_matching", tout << "anti res: " << result << "\n";);
    }

    // substitution sub_buffer(m);
    // if(smatcher(result_buffer, result, sub_buffer, pos)){
    // XXX sem_matcher is broken
    // XXX temp solution to match with syntactic equality
    // XXX is_app to filter out singletons
    if(m.are_equal(result_buffer, result) && is_app(result_buffer)) {
      TRACE("Pattern_Discovery",
            tout << "Conseq pattern found: " << result_buffer << "\n";);
    } else {
      result_buffer = result;
    }

  }
  // end of parent-matching

  /*
  app_ref clause(m);
  sem_matcher matcher(m);
  substitution diff(m);
  expr_ref constant(m);
  expr_ref varPair(m);
  expr_ref res(m);
  expr_ref_vector buf(m), buf2(m), buf3(m);
  bool dirty = false;

  for (auto &lms:p->lemmas()){

    clause = to_app(lms->get_cube()[0]);
    TRACE("spacer_adhoc_genz",
          tout << "lms->cube: " << clause << "\n"
          << "depth: " << clause->get_depth() << "\n" ;);
    if (clause->get_depth() > 2){
      constant = clause->get_arg(1);
      buf.push_back(to_app(clause->get_arg(0))->get_arg(0));
      buf.push_back(to_app(clause->get_arg(0))->get_arg(1));
      varPair = m_arith.mk_add(2, buf.c_ptr());
      buf2.push_back(varPair);
      buf2.push_back(constant);
      res = m.mk_app(clause->get_decl(), 2, buf2.c_ptr());
      buf3.push_back(res);
      dirty = true;
    }
    if(dirty){
      unsigned uses_level1;
      TRACE("spacer_adhoc_genz", tout << "merged: " << buf3 << "\n";);
      if(pt.check_inductive(lemma->level(), buf3, uses_level1, lemma->weakness())){
        TRACE("spacer_adhoc_genz", tout << "YES Inductive! \n";);
        lemma->update_cube(lemma->get_pob(), buf3);
        lemma->set_level(uses_level1);
      }
    }
  }

  //bool res = matcher(lemma->get_cube()[0], lms->get_cube()[0], diff, is_matched);

  // sem_matcher smatcher(m);

  // expr_ref minus_one(m);
  // app_ref singleVarBound(m), doubleVarBound(m);
  // expr_ref var(m);
  // expr_ref res(m);
  // expr_ref_vector buf(m), buf2(m), buf3(m);
  // bool dirty = false;

  // minus_one = m_arith.mk_numeral(rational(-1), true);

  // // expr_ref_vector core(m);
  // // core.append(lemma->get_cube());

  // pob *p = &*lemma->get_pob();

  // for (auto &lms:p->lemmas()){
  //   if (lms->get_cube().size() <= 1){
  //     continue; //Singleton lemma doesn't generalize
  //   }
  //   else {
  //     TRACE("spacer_adhoc_genz", tout
  //           << "p->lemmas: " << mk_and(lms->get_cube()) << "\n";);

  //     // FIXME sorting
  //     singleVarBound = to_app(lms->get_cube()[0]);
  //     doubleVarBound = to_app(lms->get_cube()[1]);
  //     if (doubleVarBound->get_num_args() <= 1){
  //       doubleVarBound.reset();
  //       continue;
  //     }
  //     else {
  //       TRACE("spacer_adhoc_genz", tout << "double: " << doubleVarBound << "\n";);
  //       TRACE("spacer_adhoc_genz", tout << "single: " << singleVarBound << "\n";);
  //       var = singleVarBound->get_arg(0);
  //       buf2.push_back(doubleVarBound->get_arg(0));

  //       buf.push_back(var);
  //       buf.push_back(minus_one);
  //       res = m_arith.mk_add(2, buf.c_ptr());
  //       // res = m_arith.mk_mul(2, buf.c_ptr());

  //       buf2.push_back(res);
  //       // TRACE("spacer_adhoc_genz", tout << "added: " << res << "\n";);

  //       res = m.mk_app(doubleVarBound->get_decl(), 2, buf2.c_ptr());
  //       // res = m.mk_or( m.mk_eq(buf2.get(0), var),
  //       //                m.mk_eq(buf2.get(0), buf2.get(1))) ;

  //       //Negate and push back
  //       buf3.push_back(m.mk_not(res));
  //       dirty = true;
  //     }
  //   }
  //   if(dirty){
  //     unsigned uses_level1;
  //     TRACE("spacer_adhoc_genz", tout << "merged: " << buf3 << "\n";);
  //     if(pt.check_inductive(lemma->level(), buf3, uses_level1, lemma->weakness())){
  //       TRACE("spacer_adhoc_genz", tout << "YES Inductive! \n";);
  //       lemma->update_cube(lemma->get_pob(), buf3);
  //       lemma->set_level(uses_level1);
  //     }
  //     else {
  //       TRACE("spacer_adhoc_genz", tout << "NOT Inductive:( \n";);
  //     }
  //   }
  // }

  */

  }
}
