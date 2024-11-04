/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/
#include "dfcc_infer_loop_assigns.h"

#include <util/expr.h>
#include <util/find_symbols.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

#include <analyses/goto_rw.h>
#include <goto-instrument/contracts/utils.h>
#include <goto-instrument/havoc_utils.h>

#include "dfcc_root_object.h"

/// Builds a call expression `object_whole(expr)`
static exprt
make_object_whole_call_expr(const exprt &expr, const namespacet &ns)
{
  const symbolt &object_whole_sym = ns.lookup(CPROVER_PREFIX "object_whole");
  const code_typet &object_whole_code_type =
    to_code_type(object_whole_sym.type);
  return side_effect_expr_function_callt(
    object_whole_sym.symbol_expr(),
    {{expr}},
    object_whole_code_type.return_type(),
    expr.source_location());
}

/// Returns true iff \p expr contains at least one identifier found in
/// \p identifiers.
static bool
depends_on(const exprt &expr, std::unordered_set<irep_idt> identifiers)
{
  const std::unordered_set<irep_idt> ids = find_symbol_identifiers(expr);
  for(const auto &id : ids)
  {
    if(identifiers.find(id) != identifiers.end())
      return true;
  }
  return false;
}

/// Collect identifiers that are local to this loop.
/// A identifier is or is equivalent to a loop local if
/// 1. it is declared inside the loop, or
/// 2. there is no write or read of it outside the loop.
/// 3. it is not used in loop contracts.
std::unordered_set<irep_idt> gen_loop_locals_set(
  const irep_idt &function_id,
  goto_functiont &goto_function,
  const dfcc_loop_nesting_graph_nodet &loop_node,
  message_handlert &message_handler,
  const namespacet &ns)
{
  std::unordered_set<irep_idt> loop_locals;
  std::unordered_set<irep_idt> non_loop_locals;

  const auto &loop = loop_node.instructions;

  // All identifiers declared outside the loop.
  std::unordered_set<irep_idt> non_loop_decls;
  // Ranges of all read/write outside the loop.
  rw_range_sett non_loop_rw_range_set(ns, message_handler);

  Forall_goto_program_instructions(i_it, goto_function.body)
  {
    // All variables declared in loops are loop locals.
    if(i_it->is_decl() && loop.contains(i_it))
    {
      loop_locals.insert(i_it->decl_symbol().get_identifier());
    }
    // Record all other declared variables and their ranges.
    else if(i_it->is_decl())
    {
      non_loop_decls.insert(i_it->decl_symbol().get_identifier());
    }
    // Record all writing/reading outside the loop.
    else if(
      (i_it->is_assign() || i_it->is_function_call()) && !loop.contains(i_it))
    {
      goto_rw(function_id, i_it, non_loop_rw_range_set);
    }
  }

  // Check if declared variables are loop locals.
  for(const auto &decl_id : non_loop_decls)
  {
    bool is_loop_local = true;
    // No write to the declared variable.
    for(const auto &writing_rw : non_loop_rw_range_set.get_w_set())
    {
      if(decl_id == writing_rw.first)
      {
        is_loop_local = false;
        break;
      }
    }

    // No read to the declared variable.
    for(const auto &writing_rw : non_loop_rw_range_set.get_r_set())
    {
      if(decl_id == writing_rw.first)
      {
        is_loop_local = false;
        break;
      }
    }

    const auto latch_target = loop_node.latch;

    // Loop locals are not used in loop contracts.
    for(const auto &id :
        find_symbol_identifiers(get_loop_assigns(latch_target)))
    {
      if(decl_id == id)
      {
        is_loop_local = false;
        break;
      }
    }

    for(const auto &id :
        find_symbol_identifiers(get_loop_invariants(latch_target, false)))
    {
      if(decl_id == id)
      {
        is_loop_local = false;
        break;
      }
    }

    for(const auto &id :
        find_symbol_identifiers(get_loop_decreases(latch_target, false)))
    {
      if(decl_id == id)
      {
        is_loop_local = false;
        break;
      }
    }

    // Collect all loop locals.
    if(is_loop_local)
      loop_locals.insert(decl_id);
  }

  return loop_locals;
}

assignst dfcc_infer_loop_assigns(
  const local_may_aliast &local_may_alias,
  goto_functiont &goto_function,
  const dfcc_loop_nesting_graph_nodet &loop,
  message_handlert &message_handler,
  const namespacet &ns)
{
  // infer
  assignst assigns;
  infer_loop_assigns(local_may_alias, loop.instructions, assigns);

  // compute locals
  std::unordered_set<irep_idt> loop_locals =
    gen_loop_locals_set(irep_idt(), goto_function, loop, message_handler, ns);

  // widen or drop targets that depend on loop-locals or are non-constant,
  // ie. depend on other locations assigned by the loop.
  // e.g: if the loop assigns {i, a[i]}, then a[i] is non-constant.
  havoc_utils_can_forward_propagatet is_constant(assigns, ns);
  assignst result;
  for(const auto &expr : assigns)
  {
    if(depends_on(expr, loop_locals))
    {
      // Target depends on loop locals, attempt widening to the root object
      auto root_objects = dfcc_root_objects(expr);
      for(const auto &root_object : root_objects)
      {
        if(!depends_on(root_object, loop_locals))
        {
          address_of_exprt address_of_root_object(root_object);
          address_of_root_object.add_source_location() =
            root_object.source_location();
          result.emplace(
            make_object_whole_call_expr(address_of_root_object, ns));
        }
      }
    }
    else
    {
      address_of_exprt address_of_expr(expr);
      address_of_expr.add_source_location() = expr.source_location();
      if(!is_constant(address_of_expr))
      {
        // Target address is not constant, widening to the whole object
        result.emplace(make_object_whole_call_expr(address_of_expr, ns));
      }
      else
      {
        result.emplace(expr);
      }
    }
  }

  return result;
}
