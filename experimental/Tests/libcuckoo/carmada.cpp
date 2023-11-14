// Converts C++ into Armada using clang

#include <iostream>
#include <fstream>
#include <optional>
#include <sstream>

#include "clang/AST/Stmt.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Basic/SourceManager.h"

using namespace clang;

namespace armada {

class ast_nd {
public:
  // virtual std::string print(unsigned int depth=0) const = 0;
  virtual ~ast_nd() {}
};

class expr_nd : public ast_nd {
 public:
  bool is_deref = false;
  bool is_addrof = false;
  virtual std::string print() const = 0;
};

class array_subscript_nd : public expr_nd {
 public:
  std::unique_ptr<expr_nd> base;
  std::unique_ptr<expr_nd> idx;

  virtual std::string print() const {
    return base->print() + "[" + idx->print() + "]";
  }
};

class addrof_nd : public expr_nd {
 public:
  std::unique_ptr<expr_nd> subexpr;
  bool is_addrof = true;

  virtual std::string print() const {
    return "&(" + subexpr->print() + ")";
  }
};

class deref_nd : public expr_nd {
 public:
  std::unique_ptr<expr_nd> subexpr;
  bool is_deref = true;

  virtual std::string print() const {
    return "*(" + subexpr->print() + ")";
  }
};

class paren_nd : public expr_nd {
public:
  std::unique_ptr<expr_nd> sub_expr;

  virtual std::string print() const {
    return "(" + sub_expr->print() + ")";
  }
};

class binary_op_nd : public expr_nd {
public:
  std::unique_ptr<expr_nd> lhs;
  std::unique_ptr<expr_nd> rhs;
  std::string op;

  virtual std::string print() const {
    return lhs->print() + " " + op + " " + rhs->print();
  }
};

class unary_op_nd : public expr_nd {
public:
  std::unique_ptr<expr_nd> e;
  std::string op;
  bool is_prefix;

  virtual std::string print() const {
    if (is_prefix)
      return op + e->print();
    else
      return e->print() + op;
  }
};

class stmt_nd : public ast_nd {
public:
  virtual std::string print(unsigned int depth=0) const = 0;
};

class todo_stmt_nd : public stmt_nd {
public:
  std::string todo;

  virtual std::string print(unsigned int depth=0) const
  {
    return std::string(depth*2, ' ') + "TODO_" + todo;
  }
};

class stmt_expr_nd : public stmt_nd {
public:
 std::unique_ptr<expr_nd> e;
  virtual std::string print(unsigned int depth=0) const {
    return std::string(depth*2, ' ') + e->print() + ";";
  }
};

class call_stmt_nd : public stmt_nd {
 public:
  std::vector<std::unique_ptr<expr_nd>> args;
  std::unique_ptr<expr_nd> f;
  std::string lhs;

  virtual std::string print(unsigned int depth=0) const {
    std::ostringstream ss;
    std::string prefix(2*depth, ' ');
    ss << prefix;
    if (lhs != std::string("")) {
      ss << lhs << " := ";
    }
    ss << f->print() + "(";
    for (auto iter = args.begin(); iter != args.end(); iter++) {
      if (iter != args.begin())
        ss << ", ";
      ss << (*iter)->print();
    }
    ss << ");";
    return ss.str();
  }
};

class return_nd : public stmt_nd {
public:
 std::unique_ptr<expr_nd> ret;

  virtual std::string print(unsigned int depth=0) const
  {
    if (ret != nullptr)
      return std::string(depth*2, ' ') + "return " + ret->print() + ";";
    else
      return std::string(depth*2, ' ') + "return;";
  }
};

class update_nd : public stmt_nd {
public:
  std::unique_ptr<expr_nd> lhs;
  std::unique_ptr<expr_nd> rhs;

  virtual std::string print(unsigned int depth=0) const
  {
    return std::string(depth*2, ' ') + lhs->print() + " := " + rhs->print() + ";";
  }
};

class vardecl_nd : public ast_nd {
 public:
  vardecl_nd(std::string name_in, std::string type_in)
     : name(name_in), type(type_in)
  {}

  virtual std::string print() const {
    if (is_addressable)
      return "var " + name + ":" + type + ";";
    else
      return "noaddr var " + name + ":" + type + ";";
  }

  std::string name;
  std::string type;
  bool is_addressable = false;
};

class block_nd : public stmt_nd {
public:
  std::vector<std::unique_ptr<stmt_nd>> stmts;
  virtual std::string print(unsigned int depth) const {
    std::ostringstream str;
    std::string prefix(depth*2, ' ');
    str << prefix << "{\n";

    for (const auto& stmt : stmts) {
      if (stmt != nullptr) {
        str << stmt->print(depth + 1) << "\n";
      }
    }
    str << prefix << "}\n";
    return str.str();
  }
};

class while_stmt_nd : public stmt_nd {
 public:
  std::unique_ptr<expr_nd> cond;
  std::unique_ptr<block_nd> body;

  virtual std::string print(unsigned int depth=0) const {
    std::ostringstream ss;
    std::string prefix(depth*2, ' ');
    ss << prefix << "while (" << cond->print() << ")\n";
    ss << body->print(depth);
    return ss.str();
  }
};

class method_block_nd : public block_nd {
public:
  std::vector<std::unique_ptr<vardecl_nd>> vardecls;
  std::vector<std::unique_ptr<stmt_nd>> stmts;

  virtual std::string print(unsigned int depth) const {
    std::ostringstream str;
    std::string prefix(depth*2, ' ');
    str << "{\n";

    for (const auto& vardecl : vardecls) {
      str << prefix << "  ";
      if (vardecl != nullptr) {
        str << vardecl->print() << "\n";
      }
    }

    for (const auto& stmt : stmts) {
      str << prefix;
      if (stmt != nullptr) {
        str << stmt->print(depth + 1) << "\n";
      }
    }
    str << "}\n";
    return str.str();
  }
};

class todo_expr_nd : public expr_nd {
public:
  std::string todo;
  virtual std::string print() const {
    return "TODO_expr__" + todo;
  }
};

class literal_nd : public expr_nd {
public:
  std::string literal;
  virtual std::string print() const {
    return literal;
  }
};

class if_nd : public stmt_nd {
 public:
  std::unique_ptr<expr_nd> cond;
  std::unique_ptr<stmt_nd> t;
  std::unique_ptr<stmt_nd> f;

  virtual std::string print(unsigned int depth=0) const {
    std::ostringstream ss;
    std::string prefix = std::string(depth*2, ' ');
    ss << prefix << "if (" << cond->print() << ")\n";
    if (t != nullptr)
      ss << t->print(depth);
    if (f != nullptr) {
      ss << prefix << "else\n";
      ss << f->print(depth);
    }
    return ss.str();
  }
};

class param_nd : public ast_nd {
public:
  std::string name;
  std::string type;

  virtual std::string print() const {
    return name + ":" + type;
  }
};

class params_nd : public ast_nd {
 public:
  std::vector<std::unique_ptr<param_nd>> param_nds;

  virtual std::string print() const {
    return "(TODO_params)";
  }
};

class method_nd: public ast_nd {
public:
  std::string name;
  std::unique_ptr<params_nd> params;
  std::unique_ptr<method_block_nd> block;

  virtual std::string print() const {

    std::ostringstream stream;
    stream << "method " << name;
    if (params != nullptr) {
      stream << params->print();
    } else {
      stream << "(TODO_method_params)";
    }
    if (block != nullptr) {
      stream << "\n" << block->print(0);
    } else {
      stream << "\n{\n}\n";
    }
    return stream.str();
  }
};
}

class FindNamedClassVisitor
  : public RecursiveASTVisitor<FindNamedClassVisitor> {
private:
  std::vector<std::unique_ptr<armada::vardecl_nd>> vardecls;
  int num_temps = 0;
  std::vector<std::unique_ptr<armada::stmt_nd>> *block_ctx;
  std::string class_ctx;

  std::string translate_builtin_type(const BuiltinType *bt) {
    // return std::string(bt->getNameAsCString());
    if (bt->isBooleanType()) {
      return "bool";
    } else if (bt->isCharType()) {
      return "uint8";
    }

    clang::LangOptions lang_opts;
    lang_opts.CPlusPlus = true;
    clang::PrintingPolicy policy(lang_opts);
    return std::string(bt->getNameAsCString(policy));
  }

  std::string translate_record_type(const RecordType* rt) {
    return rt->getDecl()->getNameAsString();
  }

  std::string translate_elaborated_type(const ElaboratedType* et) {
    return translate_type(et->getNamedType().getTypePtr());
  }

  std::string translate_type_concrete(const Type* type) {
    switch (type->getTypeClass()) {
      case Type::TypeClass::Typedef:
        {
        const TypedefType* tt = static_cast<const TypedefType*>(type);
        //return tt->getDecl()->getNameAsString();
        return translate_type(tt->getDecl()->getUnderlyingType().getTypePtr());
        break;
        }
      case Type::TypeClass::Builtin:
        {
          return translate_builtin_type(static_cast<const BuiltinType*>(type));
          break;
        }
      case Type::TypeClass::Record:
        {
          return translate_record_type(static_cast<const RecordType*>(type));
          break;
        }
      case Type::TypeClass::Elaborated:
        {
          return translate_elaborated_type(static_cast<const ElaboratedType*>(type));
        }
        // FIXME
      //case Type::TypeClass::ClassTemplateSpecializationClass:
        //{
          //return translate_class_tmpl_spec(static_cast<const TemplateSpecialization*>(type));
        //}
      default:
        break;
    }
    return std::string("TODO_type_") + type->getTypeClassName();
    //if (type->isTypedef()) {
    //}
    //std::cout << "Record type: " << type->isRecordType() << "\n";
    //return type->getTypeClassName();
  }

  std::string translate_type(const Type* type) {
    switch (type->getTypeClass()) {
      case Type::TypeClass::Typedef:
        {
        const TypedefType* tt = static_cast<const TypedefType*>(type);
        return tt->getDecl()->getNameAsString();
        break;
        }
      case Type::TypeClass::Builtin:
        {
          return translate_builtin_type(static_cast<const BuiltinType*>(type));
          break;
        }
      case Type::TypeClass::Record:
        {
          return translate_record_type(static_cast<const RecordType*>(type));
          break;
        }
      case Type::TypeClass::Elaborated:
        {
          return translate_elaborated_type(static_cast<const ElaboratedType*>(type));
        }
        // FIXME
      //case Type::TypeClass::ClassTemplateSpecializationClass:
        //{
          //return translate_class_tmpl_spec(static_cast<const TemplateSpecialization*>(type));
        //}
      default:
        break;
    }
    return std::string("TODO_type_") + type->getTypeClassName();
    //if (type->isTypedef()) {
    //}
    //std::cout << "Record type: " << type->isRecordType() << "\n";
    //return type->getTypeClassName();
  }

  std::unique_ptr<armada::stmt_nd> translate_decl_statement(const DeclStmt* declStmt) {
    if (declStmt->isSingleDecl()) {
      const Decl *decl = declStmt->getSingleDecl();

      if (decl->getDeclKindName() == std::string("Var")) {
        const VarDecl *varDecl = static_cast<const VarDecl*>(decl);
        const Type* type = varDecl->getTypeSourceInfo()->getType().getTypePtr();
        if (type->getTypeClass() == Type::TypeClass::LValueReference) {
          const Type* pointeeType = static_cast<const LValueReferenceType*>(type)->getPointeeType().getTypePtr();
          std::string armadaVarName = varDecl->getNameAsString() + "_ptr";
          std::string typeName = std::string("ptr<") + translate_type(pointeeType) + std::string(">");
          // auto ret = std::make_unique<armada::update_nd>();
          vardecls.push_back(std::make_unique<armada::vardecl_nd>(armadaVarName, typeName));
          if (varDecl->getInit() == nullptr)
            return nullptr;
          if (varDecl->getInit()->getStmtClass() == Stmt::StmtClass::CallExprClass ||
              varDecl->getInit()->getStmtClass() == Stmt::StmtClass::CXXMemberCallExprClass) {
            return translate_call_statement_lhs(armadaVarName, static_cast<const CallExpr*>(varDecl->getInit()));
          } else {
            auto ret = std::make_unique<armada::update_nd>();
            auto lhs = std::make_unique<armada::literal_nd>();
            lhs->literal = armadaVarName;
            ret->lhs = std::move(lhs);
            ret->rhs = make_addrof_expr(translate_expr(varDecl->getInit()));
            return ret;
          }
          return nullptr;
        }

        std::string armadaVarName = varDecl->getNameAsString();
        vardecls.push_back(std::make_unique<armada::vardecl_nd>(armadaVarName, translate_type(varDecl->getTypeSourceInfo()->getType().getTypePtr())));
        if (varDecl->getInit() == nullptr)
          return nullptr;
        if (varDecl->getInit()->getStmtClass() == Stmt::StmtClass::CallExprClass ||
            varDecl->getInit()->getStmtClass() == Stmt::StmtClass::CXXMemberCallExprClass) {
          return translate_call_statement_lhs(armadaVarName, static_cast<const CallExpr*>(varDecl->getInit()));
        } else {
          auto ret = std::make_unique<armada::update_nd>();
          auto lhs = std::make_unique<armada::literal_nd>();
          lhs->literal = armadaVarName;
          ret->lhs = std::move(lhs);
          ret->rhs = translate_expr(varDecl->getInit());
          return ret;
        }
        // std::cout << prefix << "var " << varDecl->getNameAsString() << ":" << varDecl->getTypeSourceInfo()->getType()->getTypeClassName() << ";\n";
      }
      std::cout << "VARDECL " << decl->getDeclKindName() << "\n";
    }
    vardecls.push_back(nullptr);
    return nullptr;
  }

  void init_call_stmt_rhs(std::unique_ptr<armada::call_stmt_nd> &call_stmt, const CallExpr* callExpr) {
    translate_expr_for_callee(call_stmt, callExpr->getCallee());
    add_args_to_call(call_stmt, callExpr);
  }

  void add_args_to_call(std::unique_ptr<armada::call_stmt_nd> &call_stmt, const CallExpr* callExpr) {
    unsigned int n = callExpr->getNumArgs();
    for (unsigned int i = 0; i < n; ++i) {
      call_stmt->args.push_back(translate_expr(callExpr->getArg(i)));
    }
  }

  std::unique_ptr<armada::expr_nd> translate_call_expr(const CallExpr* callExpr) {
    auto call_stmt = std::make_unique<armada::call_stmt_nd>();
    init_call_stmt_rhs(call_stmt, callExpr);

    call_stmt->lhs = std::string("temp") + std::to_string(num_temps++);
    std::string temp_typename = "TODO_return_type";
    /*
    const FunctionDecl* fdecl = callExpr->getDirectCallee();
    if (fdecl != nullptr) {
      temp_typename = "TODO_fdecl_found";
      if (!fdecl->getReturnType().isNull()) {
        temp_typename = translate_type(fdecl->getReturnType().getTypePtr());
      }
    }
    */

    /*
    if (!callExpr->getCallReturnType(*Context).isNull()) {
      std::cout << "Done!\n";
      temp_typename = "TODO_null_getTypePtr";
      if (callExpr->getCallReturnType(*Context).getTypePtr() != nullptr) {
        temp_typename = translate_type(callExpr->getCallReturnType(*Context).getTypePtr());
      }
    }
    */

    vardecls.push_back(std::make_unique<armada::vardecl_nd>(call_stmt->lhs, temp_typename));

    auto ret = std::make_unique<armada::literal_nd>();
    ret->literal = call_stmt->lhs;

    block_ctx->push_back(std::move(call_stmt));
    
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_bool_literal(const CXXBoolLiteralExpr* expr)
  {
    auto ret = std::make_unique<armada::literal_nd>();
    if (expr->getValue()) {
      ret->literal = "true";
    } else {
      ret->literal = "false";
    }
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_binary_op(const BinaryOperator* bo) {
    auto ret = std::make_unique<armada::binary_op_nd>();
    ret->lhs = translate_expr(bo->getLHS());
    ret->rhs = translate_expr(bo->getRHS());
    ret->op = bo->getOpcodeStr().str();
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_unary_op(const UnaryOperator* uo) {
    auto ret = std::make_unique<armada::unary_op_nd>();
    ret->e = translate_expr(uo->getSubExpr());
    ret->op = uo->getOpcodeStr(uo->getOpcode()).str();
    ret->is_prefix = !(uo->isPostfix());
    return ret;
  }

  std::unique_ptr<armada::call_stmt_nd> translate_call_statement_lhs(std::string lhs, const CallExpr *callExpr) {
    auto call_stmt = std::make_unique<armada::call_stmt_nd>();

    init_call_stmt_rhs(call_stmt, callExpr);
    call_stmt->lhs = lhs;
    return call_stmt;
  }

  std::unique_ptr<armada::call_stmt_nd> translate_call_statement(const Expr *lhs, const CallExpr *callExpr) {
    return translate_call_statement_lhs(translate_expr(lhs)->print(), callExpr);
  }

  std::unique_ptr<armada::stmt_nd> translate_assignment_statement(const BinaryOperator* bo) {
    auto ret = std::make_unique<armada::update_nd>();
    if (bo->getRHS()->getStmtClass() == Stmt::StmtClass::CallExprClass) {
      return translate_call_statement(bo->getLHS(), static_cast<const CallExpr*>(bo->getRHS()));
    }
    ret->lhs = translate_expr(bo->getLHS());
    ret->rhs = translate_expr(bo->getRHS());
    return ret;
  }

  std::unique_ptr<armada::expr_nd> make_addrof_expr(std::unique_ptr<armada::expr_nd> e) {
    if (armada::deref_nd* d = dynamic_cast<armada::deref_nd*>(e.get())) {
      return std::move(d->subexpr);
    }
    auto ret = std::make_unique<armada::addrof_nd>();
    ret->subexpr = std::move(e);
    return ret;
  }

  std::unique_ptr<armada::expr_nd> make_deref_expr(std::unique_ptr<armada::expr_nd> e) {
    if (armada::addrof_nd* a = dynamic_cast<armada::addrof_nd*>(e.get())) {
      return std::move(a->subexpr);
    }
    auto ret = std::make_unique<armada::deref_nd>();
    ret->subexpr = std::move(e);
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_declrefexpr(const DeclRefExpr* declref)
  {
    auto ret = std::make_unique<armada::literal_nd>();
    ret->literal = declref->getDecl()->getNameAsString();

    const Type* type = declref->getDecl()->getType().getTypePtr();
    if (type->getTypeClass() == Type::TypeClass::LValueReference) {
      ret->literal = ret->literal + "_ptr";
      return make_deref_expr(std::move(ret));
    }
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_implicitcastexpr(const ImplicitCastExpr* expr)
  {
    return translate_expr(expr->getSubExpr());
  }

  template <typename StmtType>
  void translate_member_expr_for_callee(std::unique_ptr<armada::call_stmt_nd> &c, DeclarationName memberName, const StmtType* member_expr)
  {
    if (member_expr->isImplicitAccess()) {
      auto l = std::make_unique<armada::literal_nd>();
      l->literal = memberName.getAsString();
      if (class_ctx.length() > 0) {
        l->literal = class_ctx + "_" + l->literal;
      }
      c->f = std::move(l);
      auto this_nd = std::make_unique<armada::literal_nd>();
      this_nd->literal = "this";
      c->args.push_back(std::move(this_nd));
    }
    else {
      const Expr* base =  member_expr->getBase();

      auto l = std::make_unique<armada::literal_nd>();
      l->literal = translate_type_concrete(base->getType().getTypePtr()) + "_" + memberName.getAsString();
      c->f = std::move(l);

      c->args.push_back(make_addrof_expr(translate_expr(base)));
    }
  }

  void translate_expr_for_callee(std::unique_ptr<armada::call_stmt_nd> &c, const Expr* expr) {
    switch (expr->getStmtClass()) {
      case Stmt::CXXDependentScopeMemberExprClass: {
        // return translate_dep_member_expr(static_cast<const CXXDependentScopeMemberExpr*>(expr));
        auto dme = static_cast<const CXXDependentScopeMemberExpr*>(expr);
        translate_member_expr_for_callee(c, dme->getMember(), dme);
        return;
      }
      case Stmt::UnresolvedMemberExprClass: {
        // return translate_member_expr(static_cast<const UnresolvedMemberExpr*>(expr));
        auto ume = static_cast<const UnresolvedMemberExpr*>(expr);
        translate_member_expr_for_callee(c, ume->getMemberName(), ume);
        return;
      }
      case Stmt::MemberExprClass: {
        auto me = static_cast<const MemberExpr*>(expr);
        return translate_member_expr_for_callee(c, me->getMemberDecl()->getDeclName(), me);
      }
      default:
        c->f = translate_expr(expr);
        return;
    }
  }

  template <typename StmtType>
  std::unique_ptr<armada::expr_nd> translate_member_expr(const StmtType* member_expr, DeclarationName name)
  {
    auto ret = std::make_unique<armada::literal_nd>();
    if (!member_expr->isImplicitAccess()) {
      ret->literal = translate_expr(member_expr->getBase())->print() + "." + name.getAsString();
    } else {
      ret->literal = "(*this)." + name.getAsString();
    }
    return ret;
  }

  std::string make_temp(const Type* type) {
    std::string new_name = std::string("temp") + std::to_string(num_temps++);
    vardecls.push_back(std::make_unique<armada::vardecl_nd>(new_name, translate_type(type)));
    return new_name;
  }

  std::unique_ptr<armada::expr_nd> translate_init_list_expr(const InitListExpr* expr) {
    if (expr->getType().getTypePtr()->getTypeClass() == Type::TypeClass::Record)
    {
      return translate_init_list_expr_record(expr, static_cast<const RecordType*>(expr->getType().getTypePtr()));
    }
    auto ret = std::make_unique<armada::todo_expr_nd>();
    ret->todo = "InitListExpression_nonRecord";
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_cxx_unresolved_construct_expr(const CXXUnresolvedConstructExpr* expr) {
    if (expr->getTypeAsWritten().getTypePtr()->getTypeClass() == Type::TypeClass::Record
        && expr->isListInitialization())
    {
      return translate_cxx_unresolved_construct_expr_record(expr, static_cast<const RecordType*>(expr->getTypeAsWritten().getTypePtr()));
    }
    auto ret = std::make_unique<armada::todo_expr_nd>();
    ret->todo = "ConstructExpression_nonRecord_List";
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_cxx_construct_expr(const CXXConstructExpr* expr) {
    if (expr->getType().getTypePtr()->getTypeClass() == Type::TypeClass::Record
        && expr->isListInitialization())
    {
      return translate_cxx_construct_expr_record(expr, static_cast<const RecordType*>(expr->getType().getTypePtr()));
    }
    auto ret = std::make_unique<armada::todo_expr_nd>();
    ret->todo = "ConstructExpression_nonRecord_List";
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_init_list_expr_record(const InitListExpr* inits, const RecordType *rt) {
    const RecordDecl *rd = rt->getDecl();
    std::string tempRecordName = make_temp(rt);
    int i = 0;
    for (auto curr = rd->field_begin(); curr != rd->field_end(); curr++) {
      std::string currFieldName = curr->getNameAsString();

      auto field_update = std::make_unique<armada::update_nd>();
      auto lhs = std::make_unique<armada::literal_nd>();
      lhs->literal = tempRecordName + "." + currFieldName;
      field_update->lhs = std::move(lhs);

      field_update->rhs = translate_expr(inits->getInit(i));

      block_ctx->push_back(std::move(field_update));
      i++;
      if (i >= inits->getNumInits()) break;
    }
    auto ret = std::make_unique<armada::literal_nd>();
    ret->literal = tempRecordName;
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_cxx_construct_expr_record(const CXXConstructExpr* expr, const RecordType *rt) {
    auto inits = static_cast<const InitListExpr*>(expr->getArg(0));
    return translate_init_list_expr_record(inits, rt);
  }

  std::unique_ptr<armada::expr_nd> translate_cxx_unresolved_construct_expr_record(const CXXUnresolvedConstructExpr* expr, const RecordType *rt) {
    auto inits = static_cast<const InitListExpr*>(expr->getArg(0));
    return translate_init_list_expr_record(inits, rt);
  }

  std::unique_ptr<armada::expr_nd> translate_array_subscript(const ArraySubscriptExpr* subscript_expr) {
    auto ret = std::make_unique<armada::array_subscript_nd>();
    ret->base = translate_expr(subscript_expr->getIdx());
    ret->idx = translate_expr(subscript_expr->getBase());
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_paren_expr(const ParenExpr* paren_expr) {
    auto ret = std::make_unique<armada::paren_nd>();
    ret->sub_expr = translate_expr(paren_expr->getSubExpr());
    return ret;
  }

  std::unique_ptr<armada::expr_nd> translate_expr(const Expr* expr) {
    switch (expr->getStmtClass()) {
      case Stmt::IntegerLiteralClass: {
        auto ret = std::make_unique<armada::literal_nd>();
        ret->literal = static_cast<const IntegerLiteral*>(expr)->getValue().toString(10, true);
        return ret;
        break;
      }
      case Stmt::CXXBoolLiteralExprClass: {
        return translate_bool_literal(static_cast<const CXXBoolLiteralExpr*>(expr));
        break;
      }
      case Stmt::BinaryOperatorClass: {
        const BinaryOperator *bo = static_cast<const BinaryOperator*>(expr);
        if (bo->isAssignmentOp()) {
          return nullptr;
        }
        return translate_binary_op(bo);
      }
      case Stmt::UnaryOperatorClass: {
        const UnaryOperator *uo = static_cast<const UnaryOperator*>(expr);
        return translate_unary_op(uo);
      }
      case Stmt::DeclRefExprClass: {
        return translate_declrefexpr(static_cast<const DeclRefExpr*>(expr));
      }
      case Stmt::ImplicitCastExprClass: {
        return translate_implicitcastexpr(static_cast<const ImplicitCastExpr*>(expr));
      }
      case Stmt::CXXMemberCallExprClass:
      case Stmt::CallExprClass: {
        return translate_call_expr(static_cast<const CallExpr*>(expr));
      }
      case Stmt::CXXDependentScopeMemberExprClass: {
        auto e = static_cast<const CXXDependentScopeMemberExpr*>(expr);
        return translate_member_expr(e, e->getMember());
      }
      case Stmt::MemberExprClass: {
        auto e = static_cast<const MemberExpr*>(expr);
        return translate_member_expr(e, e->getMemberDecl()->getDeclName());
      }
      case Stmt::UnresolvedMemberExprClass: {
        auto e = static_cast<const UnresolvedMemberExpr*>(expr);
        return translate_member_expr(e, e->getMemberName());
      }
      case Stmt::CXXUnresolvedConstructExprClass: {
        return translate_cxx_unresolved_construct_expr(static_cast<const CXXUnresolvedConstructExpr*>(expr));
      }
      case Stmt::CXXConstructExprClass: {
        return translate_cxx_construct_expr(static_cast<const CXXConstructExpr*>(expr));
      }
      case Stmt::InitListExprClass: {
        return translate_init_list_expr(static_cast<const InitListExpr*>(expr));
      }
      case Stmt::ArraySubscriptExprClass: {
        return translate_array_subscript(static_cast<const ArraySubscriptExpr*>(expr));
      }
      case Stmt::ParenExprClass: {
        return translate_paren_expr(static_cast<const ParenExpr*>(expr));
      }
      case Stmt::ExprWithCleanupsClass: {
        return translate_expr(static_cast<const ExprWithCleanups*>(expr)->getSubExpr());
      }
      default:
        break;
    }

    auto ret = std::make_unique<armada::todo_expr_nd>();
    if (!expr->getType().isNull())  {
      ret->todo = expr->getStmtClassName() + std::string(":") + translate_type(expr->getType().getTypePtr());
    } else {
      ret->todo = std::string(expr->getStmtClassName()) + ":unknown type";
    }
    return ret;
  }

  std::unique_ptr<armada::if_nd> translate_if_statement(const IfStmt* ifStmt) {
    auto i = std::make_unique<armada::if_nd>();
    i->cond = translate_expr(ifStmt->getCond());
    i->t = translate_statement(ifStmt->getThen());
    i->f = translate_statement(ifStmt->getElse());
    return std::move(i);
  }

  std::unique_ptr<armada::return_nd> translate_return_statement(const ReturnStmt* return_stmt) {
    auto ret = std::make_unique<armada::return_nd>();
    ret->ret = nullptr;
    if (return_stmt->getRetValue() != nullptr) {
      ret->ret = translate_expr(return_stmt->getRetValue());
    }
    return ret;
  }

  std::unique_ptr<armada::while_stmt_nd> translate_while_statement(const WhileStmt *stmt) {
    auto ret = std::make_unique<armada::while_stmt_nd>();
    ret->cond = translate_expr(stmt->getCond());
    const Stmt *body = stmt->getBody();
    if (body->getStmtClass() == Stmt::CompoundStmtClass) {
      ret->body = translate_compound_statement(static_cast<const CompoundStmt*>(stmt->getBody()));
    } else {
      ret->body = std::make_unique<armada::block_nd>();
      ret->body->stmts.push_back(translate_statement(stmt->getBody()));
    }
    return ret;
  }

  std::unique_ptr<armada::while_stmt_nd> translate_for_statement(const ForStmt *stmt) {
    auto ret = std::make_unique<armada::while_stmt_nd>();

    ret->cond = translate_expr(stmt->getCond());
    block_ctx->push_back(translate_statement(stmt->getInit()));

    const Stmt *body = stmt->getBody();
    if (body != nullptr) {
      if (body->getStmtClass() == Stmt::CompoundStmtClass) {
        ret->body = translate_compound_statement(static_cast<const CompoundStmt*>(stmt->getBody()));
        if (stmt->getInc() != nullptr)
          ret->body->stmts.push_back(translate_statement(stmt->getInc()));
      } else {
        ret->body = std::make_unique<armada::block_nd>();
        ret->body->stmts.push_back(translate_statement(stmt->getBody()));
        if (stmt->getInc() != nullptr)
          ret->body->stmts.push_back(translate_statement(stmt->getInc()));
      }
    } else {
      ret->body = nullptr;
    }
    return ret;
  }

  std::unique_ptr<armada::stmt_nd> make_stmt_expr(std::unique_ptr<armada::expr_nd> expr) {
    auto ret = std::make_unique<armada::stmt_expr_nd>();
    ret->e = std::move(expr);
    return ret;
  }

  std::unique_ptr<armada::stmt_nd> translate_no_lhs_call(const CallExpr *callExpr) {
    auto ret = std::make_unique<armada::call_stmt_nd>();
    init_call_stmt_rhs(ret, callExpr);
    ret->lhs = "";
    return ret;
  }

  std::unique_ptr<armada::stmt_nd> translate_statement(const Stmt* stmt) {
    if (stmt == nullptr) {
      return nullptr;
    }
    switch (stmt->getStmtClass())
    {
      case Stmt::DeclStmtClass: {
        const DeclStmt *declStmt = static_cast<const DeclStmt*>(stmt);
        auto s = translate_decl_statement(declStmt);
        return s;
        break;
      }
      case Stmt::CompoundStmtClass: {
        return translate_compound_statement(static_cast<const CompoundStmt*>(stmt));
        break;
      }
      case Stmt::IfStmtClass: {
        return translate_if_statement(static_cast<const IfStmt*>(stmt));
        break;
      }
      case Stmt::ReturnStmtClass: {
        return translate_return_statement(static_cast<const ReturnStmt*>(stmt));
        break;
      }
      case Stmt::BinaryOperatorClass: {
        const BinaryOperator *bo = static_cast<const BinaryOperator*>(stmt);
        if (bo->isAssignmentOp()) {
          return translate_assignment_statement(bo);
        }
      }
      case Stmt::WhileStmtClass: {
        return translate_while_statement(static_cast<const WhileStmt*>(stmt));
      }
      case Stmt::ForStmtClass: {
        return translate_for_statement(static_cast<const ForStmt*>(stmt));
      }
      case Stmt::CallExprClass: {
        return translate_no_lhs_call(static_cast<const CallExpr*>(stmt));
      }
      case Stmt::CXXMemberCallExprClass: {
        return translate_no_lhs_call(static_cast<const CallExpr*>(stmt));
      }
      case Stmt::UnaryOperatorClass: {
        return make_stmt_expr(translate_expr(static_cast<const Expr*>(stmt)));
      }
      default: {
        break;
      }
    }

    auto ret = std::make_unique<armada::todo_stmt_nd>();
    ret->todo = stmt->getStmtClassName();
    return ret;
  }

  std::unique_ptr<armada::block_nd> translate_compound_statement(const CompoundStmt* compoundStmt) {
    auto ret = std::make_unique<armada::block_nd>();
    CompoundStmt::const_body_iterator curr = compoundStmt->body_begin();
    CompoundStmt::const_body_iterator end = compoundStmt->body_end();
    while (curr != end) {
      block_ctx = &(ret->stmts);
      const Stmt* stmt = *curr;
      auto s = translate_statement(*curr);
      if (s != nullptr) {
        ret->stmts.push_back(std::move(s));
      }
      curr++;
    }
    return ret;
  }

  std::unique_ptr<armada::method_nd> translate_method_decl(CXXMethodDecl *decl) {
    FullSourceLoc FullLocation = Context->getFullLoc(decl->getBeginLoc());
    if (FullLocation.isValid()) {
      std::cout << "\n\n// Found declaration of `" << decl->getQualifiedNameAsString() << "' at "
          << FullLocation.getSpellingLineNumber() << ":"
          << FullLocation.getSpellingColumnNumber() << "\n";
    }

    class_ctx = "";
    num_temps = 0;
    std::string armadaMethodName = decl->getNameAsString();
    CXXRecordDecl* parent = decl->getParent();
    if (parent) {
      class_ctx = parent->getNameAsString();
      armadaMethodName = class_ctx + "_" + armadaMethodName;
    }

    vardecls.clear();
    std::unique_ptr<armada::method_nd> m = std::make_unique<armada::method_nd>();
    m->name = armadaMethodName;
    m->params = nullptr;

    clang::Stmt *methodBody = decl->getBody();
    if (methodBody == nullptr) {
      m->block = nullptr;
    } else {
      m->block = std::make_unique<armada::method_block_nd>();
      m->block->stmts = std::move(translate_compound_statement(static_cast<CompoundStmt*>(methodBody))->stmts);
      m->block->vardecls = std::move(vardecls);
    }
    return m;
  }

public:
  explicit FindNamedClassVisitor(ASTContext *Context)
    : Context(Context) {}

  bool VisitCXXMethodDecl(CXXMethodDecl *decl) {
    auto m = translate_method_decl(decl);
    std::cout << m->print();
    return true;
  }

private:
  ASTContext *Context;
};

class FindNamedClassConsumer : public clang::ASTConsumer {
public:
  explicit FindNamedClassConsumer(clang::SourceManager &SM, ASTContext *Context)
    : sourceManager(SM), Visitor(Context) {}

  virtual void HandleTranslationUnit(clang::ASTContext &Context) {
    auto Decls = Context.getTranslationUnitDecl()->decls();
    for (auto &Decl : Decls) {
      const auto& FileID = sourceManager.getFileID(Decl->getLocation());
      if (FileID != sourceManager.getMainFileID())
        continue;
      Visitor.TraverseDecl(Decl);
    }
  }
private:
  clang::SourceManager &sourceManager;
  FindNamedClassVisitor Visitor;
};

class FindNamedClassAction : public clang::ASTFrontendAction {
public:
  virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
    clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    return std::unique_ptr<clang::ASTConsumer>(
        new FindNamedClassConsumer(Compiler.getSourceManager(), &Compiler.getASTContext()));
  }
};

int main(int argc, char **argv) {
  std::ios::sync_with_stdio(true);
  if (argc > 1) {
    std::ifstream t(argv[1]);
    std::string source((std::istreambuf_iterator<char>(t)),
                     std::istreambuf_iterator<char>());
    clang::tooling::runToolOnCode(new FindNamedClassAction(), source);
  }
}
