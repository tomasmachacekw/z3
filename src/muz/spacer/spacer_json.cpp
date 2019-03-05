/**++
Copyright (c) 2017 Microsoft Corporation and Matteo Marescotti

Module Name:

    spacer_json.cpp

Abstract:

    SPACER json marshalling support

Author:

    Matteo Marescotti

Notes:

--*/

#include <iomanip>
#include "spacer_context.h"
#include "spacer_json.h"
#include "spacer_util.h"

#include "ast/ast.h"


namespace spacer {

static std::ostream &json_marshal(std::ostream &out, ast *t, ast_manager &m) {

    mk_epp pp = mk_epp(t, m);
    std::ostringstream ss;
    ss << pp;
    out << "\"";
    for (auto &c:ss.str()) {
        switch (c) {
        case '"':
            out << "\\\"";
            break;
        case '\\':
            out << "\\\\";
            break;
        case '\b':
            out << "\\b";
            break;
        case '\f':
            out << "\\f";
            break;
        case '\n':
            out << "\\n";
            break;
        case '\r':
            out << "\\r";
            break;
        case '\t':
            out << "\\t";
            break;
        default:
            if ('\x00' <= c && c <= '\x1f') {
                out << "\\u"
                    << std::hex << std::setw(4) << std::setfill('0') << (int) c;
            } else {
                out << c;
            }
        }
    }
    out << "\"";
    return out;
}

unsigned count_lits(const app * pred, ast_manager &m) {
    unsigned n = pred->get_num_args();
    unsigned num_lits = 0;
    for (unsigned i = 0; i < n; i++) {
        expr * e = pred->get_arg(i);
        if(is_app(e)){
          family_id fid = to_app(e)->get_family_id();
          if(to_app(e)->get_num_args() == 0 && fid == null_family_id)
            num_lits ++;
          else{
            num_lits += count_lits(to_app(e), m);
          }
        }
    }
    return num_lits;
}


static std::ostream &json_marshal(std::ostream &out, lemma *l) {

  TRACE("spacer_adhoc_genz", tout
        << "get_expr: " << mk_pp(l->get_expr(), l->get_ast_manager())
        << "\n";);

    out << "{"
        << R"("init_level":")" << l->init_level()
        << R"(", "level":")" << l->level()
        << R"(", "cluster":")" << l->cluster()
        << R"(", "num_vars":")" << count_lits(to_app(l->get_expr()), l->get_ast_manager())
        << R"(", "expr":)";
    json_marshal(out, l->get_expr(), l->get_ast_manager());

    // XXX field RAW pob => not sure if we ever want to have this
    out << R"(, "pob":)";
    if(l->has_pob()) {
        pob_ref p = l->get_pob();
        // std::ostringstream pob_expr;
        // json_marshal(pob_expr, p->post(), p->get_ast_manager());
        // out << pob_expr.str();
        out << R"(")" << p->post()->get_id() <<  R"(")" ;
    }

    out << "}";
    return out;
}

static std::ostream &json_marshal(std::ostream &out, const lemma_ref_vector &lemmas) {

        std::ostringstream ls;
        for (auto l:lemmas) {
            ls << ((unsigned)ls.tellp() == 0 ? "" : ",");
            json_marshal(ls, l);
        }
        out << "[" << ls.str() << "]";
        return out;
    }


void json_marshaller::register_lemma(lemma *l) {
    if (l->has_pob()) {
        m_relations[&*l->get_pob()][l->get_pob()->depth()].push_back(l);
    }
}

void json_marshaller::register_pob(pob *p) {
    m_relations[p];
}

void json_marshaller::marshal_lemmas_old(std::ostream &out) const {
    unsigned pob_id = 0;
    for (auto &pob_map:m_relations) {
        std::ostringstream pob_lemmas;
        for (auto &depth_lemmas : pob_map.second) {
            pob_lemmas << ((unsigned)pob_lemmas.tellp() == 0 ? "" : ",")
                       << "\"" << depth_lemmas.first << "\":";
            json_marshal(pob_lemmas, depth_lemmas.second);
        }
        if (pob_lemmas.tellp()) {
            out << ((unsigned)out.tellp() == 0 ? "" : ",\n");
            out << "\"" << pob_id << "\":{" << pob_lemmas.str() << "}";
        }
        pob_id++;
    }
}
void json_marshaller::marshal_lemmas_new(std::ostream &out) const {
    unsigned pob_id = 0;
    for (auto &pob_map:m_relations) {
        std::ostringstream pob_lemmas;
        pob *n = pob_map.first;
        unsigned i = 0;
        for (auto *l : n->lemmas()) {
            pob_lemmas << ((unsigned)pob_lemmas.tellp() == 0 ? "" : ",")
                       << "\"" << i++ << "\":";
            lemma_ref_vector lemmas_vec;
            lemmas_vec.push_back(l);
            json_marshal(pob_lemmas, lemmas_vec);
        }

        if (pob_lemmas.tellp()) {
            out << ((unsigned)out.tellp() == 0 ? "" : ",\n");
            out << "\"" << pob_id << "\":{" << pob_lemmas.str() << "}";
        }
        pob_id++;
    }
}

std::ostream &json_marshaller::marshal(std::ostream &out) const {
    std::ostringstream nodes;
    std::ostringstream edges;
    std::ostringstream lemmas;

    if (m_old_style)
        marshal_lemmas_old(lemmas);
    else
        marshal_lemmas_new(lemmas);

    unsigned pob_id = 0;
    unsigned depth = 0;
    while (true) {
        double root_expand_time = m_ctx->get_root().get_expand_time(depth);
        bool a = false;
        pob_id = 0;
        for (auto &pob_map:m_relations) {
            pob *n = pob_map.first;
            double expand_time = n->get_expand_time(depth);
            if (expand_time > 0) {
                a = true;
                std::ostringstream pob_expr;
                json_marshal(pob_expr, n->post(), n->get_ast_manager());

                nodes << ((unsigned)nodes.tellp() == 0 ? "" : ",\n") <<
                    "{\"id\":\"" << depth << n <<
                    "\",\"relative_time\":\"" << expand_time / root_expand_time <<
                    "\",\"absolute_time\":\"" << std::setprecision(2) << expand_time <<
                    "\",\"predicate\":\"" << n->pt().head()->get_name() <<
                    "\",\"expr_id\":\"" << n->post()->get_id() <<
                    "\",\"pob_id\":\"" << pob_id <<
                    "\",\"depth\":\"" << depth << // XXX This doesn't feel right! why loggin same id and depth?
                    "\",\"expr\":" << pob_expr.str() << "}";
                if (n->parent()) {
                    edges << ((unsigned)edges.tellp() == 0 ? "" : ",\n") <<
                        "{\"from\":\"" << depth << n->parent() <<
                        "\",\"to\":\"" << depth << n << "\"}";
                }
            }
            pob_id++;
        }
        if (!a) {
            break;
        }
        depth++;
    }
    out << "{\n\"nodes\":[\n" << nodes.str() << "\n],\n";
    out << "\"edges\":[\n" << edges.str() << "\n],\n";
    out << "\"lemmas\":{\n" << lemmas.str() << "\n}\n}\n";
    // XXX maybe we want flatten lemmas here for LemmaVis
    return out;
}

}
