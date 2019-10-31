/*
 Copyright 2019 Alain Dargelas
 
 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at
 
 http://www.apache.org/licenses/LICENSE-2.0
 
 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 */

/* 
 * File:   TestbenchElaboration.cpp
 * Author: alain
 * 
 * Created on February 6, 2019, 9:01 PM
 */

#include <queue>

#include "../SourceCompile/VObjectTypes.h"
#include "../Design/VObject.h"
#include "../Library/Library.h"
#include "../Design/FileContent.h"
#include "../SourceCompile/SymbolTable.h"
#include "../ErrorReporting/Error.h"
#include "../ErrorReporting/Location.h"
#include "../ErrorReporting/Error.h"
#include "../ErrorReporting/ErrorDefinition.h"
#include "../ErrorReporting/ErrorContainer.h"
#include "../SourceCompile/CompilationUnit.h"
#include "../SourceCompile/PreprocessFile.h"
#include "../SourceCompile/CompileSourceFile.h"
#include "../SourceCompile/ParseFile.h"
#include "../SourceCompile/Compiler.h"
#include "CompileDesign.h"
#include "../Testbench/Property.h"
#include "../Design/Function.h"
#include "../Testbench/ClassDefinition.h"
#include "TestbenchElaboration.h"

using namespace SURELOG;


TestbenchElaboration::~TestbenchElaboration () { }


bool TestbenchElaboration::bindTypedefs_() {
  Compiler* compiler = m_compileDesign->getCompiler ();
  ErrorContainer* errors = compiler->getErrorContainer ();
  SymbolTable* symbols = compiler->getSymbolTable ();
  Design* design = compiler->getDesign();

  std::vector<std::pair < TypeDef*, DesignComponent*>> defs;

  for (auto file : design->getAllFileContents ())
    {
      FileContent* fC = file.second;
      for (auto typed : fC ->getTypeDefMap ())
        {
          TypeDef* typd = typed.second;
          defs.push_back (std::make_pair (typd, fC));
        }
    }

  for (auto package : design->getPackageDefinitions ())
    {
      Package* pack = package.second;
      for (auto typed : pack->getTypeDefMap ())
        {
          TypeDef* typd = typed.second;
          defs.push_back (std::make_pair (typd, pack));
        }
    }

  for (auto program_def : design->getProgramDefinitions ())
    {
      Program* program = program_def.second;
      for (auto typed : program->getTypeDefMap ())
        {
          TypeDef* typd = typed.second;
          defs.push_back (std::make_pair (typd, program));
        }
    }

  for (auto class_def : design->getClassDefinitions ())
    {
      ClassDefinition* classp = class_def.second;
      for (auto typed : classp->getTypeDefMap ())
        {
          TypeDef* typd = typed.second;
          defs.push_back (std::make_pair (typd, classp));
        }
    }


  for (auto def : defs)
    {
      TypeDef* typd = def.first;
      DesignComponent* comp = def.second;
      if (typd->getDefinition () == NULL)
        {
          DataType* def = bindTypeDef_ (typd, comp, ErrorDefinition::NO_ERROR_MESSAGE);
          if (def && (typd != def))
            {
              typd->setDefinition (def);
            }
          else
            {
              FileContent* fC = typd->getFileContent ();
              NodeId id = typd->getNodeId ();
              std::string fileName = fC->getFileName (id);
              unsigned int line = fC->Line (id);
              std::string definition_string;
              NodeId defNode = typd->getDefinitionNode ();
              VObjectType defType = fC->Type (defNode);
              if (defType == VObjectType::slStringConst)
                {
                  definition_string = fC->SymName (defNode);
                }
              Location loc1 (symbols->registerSymbol (fileName), line, 0, symbols->registerSymbol (definition_string));
              Error err1 (ErrorDefinition::COMP_UNDEFINED_TYPE, loc1);
              errors->addError (err1);
            }
        }
    }

  
  return true;
}

bool checkValidFunction(DataType* dtype, std::string function,
                        Statement* stmt, Design* design, std::string& datatypeName)
{
  bool validFunction = true;
  VObjectType type = dtype->getType ();
  DataType* def = dtype->getDefinition ();
  if (type == VObjectType::slClass_declaration)
    {
      ClassDefinition* the_class = dynamic_cast<ClassDefinition*> (dtype);
      if (the_class)
        {
          Function* func = the_class->getFunction (function);
          if (func)
            stmt->setFunction (func);
          else
            validFunction = false;
        }
      else
        {
          the_class = dynamic_cast<ClassDefinition*> (def);
          if (the_class)
            {
              Function* func = the_class->getFunction (function);
              if (func)
                stmt->setFunction (func);
              else
                validFunction = false;
            }

        }
    }
  else if (dtype->isString_type (type))
    {
      ClassDefinition* array = design->getClassDefinition ("builtin::string");
      Function* func = array->getFunction (function);
      if (func)
        stmt->setFunction (func);
      else
        {
          datatypeName = "string";
          validFunction = false;
        }
    }
  else
    validFunction = false;
  return validFunction;
}

bool checkValidBuiltinClass_(std::string classname, std::string function, 
                             Statement* stmt, Design* design, std::string& datatypeName)
{
  bool validFunction = true;
  ClassDefinition* array = design->getClassDefinition ("builtin::" + classname);
  Function* func = array->getFunction (function);
  if (func)
    stmt->setFunction (func);
  else
    {
      datatypeName = classname;
      validFunction = false;
    }
  return validFunction;
}

void computeVarChain(FileContent* fC, NodeId nodeId, std::vector<std::string>& var_chain) {
  while (nodeId)
    {
      VObjectType type = fC->Type(nodeId);
      switch (type)
        {
        case VObjectType::slStringConst:
        {
          var_chain.push_back (fC->SymName(nodeId));
          break;
        }
        case VObjectType::slImplicit_class_handle:
        {
          NodeId child = fC->Child(nodeId);
          VObjectType childType = fC->Type(child);
          if (childType == VObjectType::slThis_keyword)
            var_chain.push_back("this");
          else if (childType == VObjectType::slSuper_keyword)
            var_chain.push_back("super");
          else 
            var_chain.push_back("UNKNOWN_TYPE");
          break;
        }
        default:
          var_chain.push_back("UNKNOWN_NAME");
          break;
        }
      nodeId = fC->Sibling(nodeId);
    }
} 

bool TestbenchElaboration::bindClasses_() {
  checkForMultipleDefinition_();
  bindBaseClasses_();
  bindDataTypes_();
  bindFunctions_();
  bindTasks_();
  return true;
}
  
bool TestbenchElaboration::checkForMultipleDefinition_() {
  Compiler* compiler = m_compileDesign->getCompiler ();
  ErrorContainer* errors = compiler->getErrorContainer ();
  SymbolTable* symbols = compiler->getSymbolTable ();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions ();  

  // Check for multiple definition
  std::string prevClassName = "";
  ClassDefinition* prevClassDefinition = NULL;
  for (ClassNameClassDefinitionMultiMap::iterator itr = classes.begin(); itr != classes.end(); itr++)
    {
      std::string className = (*itr).first;
      ClassDefinition* classDefinition = (*itr).second;
      bool done = false;
      if (className == prevClassName)
        {
          
          FileContent* fC1 = classDefinition->getFileContents()[0];
          NodeId nodeId1 = classDefinition->getNodeIds()[0];
          std::string fileName1 = fC1->getFileName (nodeId1);
          unsigned int line1 = fC1->Line (nodeId1);
          Location loc1 (symbols->registerSymbol (fileName1), line1, 0, symbols->registerSymbol (className));

          std::vector<Location> locations;
          
          while (1)
            {

              FileContent* fC2 = prevClassDefinition->getFileContents ()[0];
              NodeId nodeId2 = prevClassDefinition->getNodeIds ()[0];
              std::string fileName2 = fC2->getFileName (nodeId2);
              unsigned int line2 = fC2->Line (nodeId2);
              Location loc2 (symbols->registerSymbol (fileName2), line2, 0, symbols->registerSymbol (className));

              if ((fileName1 != fileName2) || (line1 != line2))
                {
                  std::string diff;
                  if (fC1->diffTree (diff, nodeId1, fC2, nodeId2))
                    {
                      locations.push_back(loc2);
                    }
                }
              
              itr++;
              if (itr == classes.end())
                {
                  done = true;
                  break;
                }
              else 
                {
                  std::string nextClassName = (*itr).first;
                  ClassDefinition* nextClassDefinition = (*itr).second;
                  prevClassName = nextClassName;
                  prevClassDefinition = nextClassDefinition;
                  if (prevClassName != className)
                    {
                      className = prevClassName;
                      classDefinition = prevClassDefinition;
                      break;
                    }
                }             
            }
          
          if (locations.size())
            {
              Error err1 (ErrorDefinition::COMP_MULTIPLY_DEFINED_CLASS, loc1, &locations);
              errors->addError (err1);
            }                
        }
      prevClassName = className;
      prevClassDefinition = classDefinition;
      if (done)
        break;
    }
  return true;
}


bool TestbenchElaboration::bindBaseClasses_() {
  Compiler* compiler = m_compileDesign->getCompiler ();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions ();
 
  // Bind base classes
  for (ClassNameClassDefinitionMultiMap::iterator itr = classes.begin(); itr != classes.end(); itr++)
    {
      std::string className = (*itr).first;
      ClassDefinition* classDefinition = (*itr).second;
      for (auto& class_def : classDefinition->getBaseClassMap ())
        {         
          DataType* the_def = bindDataType_(class_def.first, class_def.second->getFileContent (),
                                            class_def.second->getNodeId (),
                                            classDefinition, ErrorDefinition::COMP_UNDEFINED_BASE_CLASS);
          class_def.second = dynamic_cast<ClassDefinition*> (the_def); 
          if(class_def.second)
            {
              // Super
              DataType* thisdt = new DataType (class_def.second->getFileContent (), class_def.second->getNodeId (), class_def.second->getName (), VObjectType::slClass_declaration);
              thisdt->setDefinition (class_def.second);
              Property* prop = new Property (thisdt, classDefinition->getFileContent (), classDefinition->getNodeId(), 0, "super", false, false,
                                             false, false, false);
              classDefinition->insertProperty (prop);
            }
          else 
            {
              class_def.second = dynamic_cast<Parameter*> (the_def);
              if (class_def.second)
                {
                  // Super
                  DataType* thisdt = new DataType (class_def.second->getFileContent (), class_def.second->getNodeId (), class_def.second->getName (), VObjectType::slClass_declaration);
                  thisdt->setDefinition (class_def.second);
                  Property* prop = new Property (thisdt, classDefinition->getFileContent (), classDefinition->getNodeId (), 0, "super", false, false,
                                                 false, false, false);
                  classDefinition->insertProperty (prop);
                }
            }
        }
    }
  return true;
}

bool TestbenchElaboration::bindDataTypes_() {
  Compiler* compiler = m_compileDesign->getCompiler ();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions ();  

   // Bind data types
   for (ClassNameClassDefinitionMultiMap::iterator itr = classes.begin(); itr != classes.end(); itr++)
    {
      std::string className = (*itr).first;
      ClassDefinition* classDefinition = (*itr).second;

      for (auto& datatype : classDefinition->getUsedDataTypeMap ())
        {
          std::string dataTypeName = datatype.first;
          DataType* dtype = datatype.second;
          if (dtype->getDefinition ())
            continue;
          VObjectType type = dtype->getType ();
          if (type == VObjectType::slStringConst ||
              type == VObjectType::slNull_rule ||
              type == VObjectType::slClass_scope)
            {
              DataType* the_def = bindDataType_ (dataTypeName, dtype->getFileContent (), dtype->getNodeId (),
                                                 classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
              if (the_def != dtype)
                dtype->setDefinition (the_def);
            }
        }
       for (auto& func : classDefinition->getFunctionMap ())
        {
          for (auto& datatype : func.second->getUsedDataTypeMap ())
            {
              std::string dataTypeName = datatype.first;
              DataType* dtype = datatype.second;
              if (dtype->getDefinition ())
                continue;
              VObjectType type = dtype->getType ();
              if (type == VObjectType::slStringConst ||
                  type == VObjectType::slNull_rule ||
                  type == VObjectType::slClass_scope)
                {
                  DataType* the_def = bindDataType_ (dataTypeName, dtype->getFileContent (), dtype->getNodeId (),
                                                     classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
                  if (the_def != dtype)
                    dtype->setDefinition (the_def);
                }
            }
         }
     }
  return true;
}


bool TestbenchElaboration::bindFunctions_() {
  bindFunctionReturnTypesAndParamaters_();
  bindFunctionBodies_();
  return true;
}

bool TestbenchElaboration::bindFunctionReturnTypesAndParamaters_() {  
  Compiler* compiler = m_compileDesign->getCompiler ();
  ErrorContainer* errors = compiler->getErrorContainer ();
  SymbolTable* symbols = compiler->getSymbolTable ();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions ();  
  
   // Bind Function return values, parameters and body
   for (ClassNameClassDefinitionMultiMap::iterator itr = classes.begin(); itr != classes.end(); itr++)
    {
      std::string className = (*itr).first;
      ClassDefinition* classDefinition = (*itr).second;
      for (auto& func : classDefinition->getFunctionMap ())
        {
          DataType* dtype = func.second->getReturnType ();
          std::string dataTypeName = dtype->getName ();
          if (dtype->getDefinition ())
            continue;
          if (dtype->getFileContent () == NULL)
            continue;
          if (dtype->getType () == VObjectType::slStringConst) 
            {
              DataType* the_def = bindDataType_ (dataTypeName, dtype->getFileContent (), func.second->getNodeId (),
                                                 classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
              if (the_def != dtype)
                dtype->setDefinition (the_def);
            }
          for (auto& param : func.second->getParams ())
            {
              DataType* dtype = param->getDataType ();
              std::string dataTypeName = dtype->getName ();
              if (dtype->getDefinition ())
                continue;
              if (dtype->getFileContent () == NULL)
                continue;
              if (dtype->getType () == VObjectType::slStringConst)
                {
                  DataType* the_def = bindDataType_ (dataTypeName, dtype->getFileContent (), param->getNodeId (),
                                                     classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
                  if (the_def != dtype)
                    dtype->setDefinition (the_def);
                  if (the_def && the_def->isParameter ())
                    continue;
                  Value* value = param->getDefault ();
                  if (value)
                    {
                      if (!dtype->isCompatible (value))
                        {
                          std::string name = param->getName ();
                          std::string typeName = dtype->getName ();
                          NodeId p = param->getNodeId ();
                          FileContent* fC = dtype->getFileContent ();
                          std::string fileName = fC->getFileName (p);
                          unsigned int line = fC->Line (p);
                          Location loc1 (symbols->registerSymbol (fileName), line, 0, symbols->registerSymbol (name + " of type " + typeName));
                          std::string exp;
                          if (value->getType () == Value::String)
                            exp = value->getValueS ();
                          else if (value->getType () == Value::Double)
                            exp = std::to_string (value->getValueD (0));
                          else
                            exp = std::to_string (value->getValueL (0));
                          Location loc2 (0, 0, 0, symbols->registerSymbol (exp));
                          Error err1 (ErrorDefinition::COMP_INCOMPATIBLE_TYPES, loc1, loc2);
                          errors->addError (err1);
                        }
                    }
                }
            }
        }
     }
  return true;
}

bool TestbenchElaboration::bindSubRoutineCall_(ClassDefinition* classDefinition, Statement* stmt, Design* design, SymbolTable* symbols, ErrorContainer* errors)
{
  std::string datatypeName;
  SubRoutineCallStmt* st = dynamic_cast<SubRoutineCallStmt*> (stmt);
  std::vector<std::string> var_chain = st->getVarChainNames ();
  std::string function = st->getFunc ();
  bool validFunction = true;
  DataType* dtype = NULL;
  Variable* the_obj = NULL;
  if (st->isStatic ())
    the_obj = locateStaticVariable_ (var_chain, st->getFileContent (), st->getNodeId (), stmt->getScope (), classDefinition, ErrorDefinition::ELAB_UNDEF_VARIABLE);
  else
    the_obj = locateVariable_ (var_chain, st->getFileContent (), st->getNodeId (), stmt->getScope (), classDefinition, ErrorDefinition::ELAB_UNDEF_VARIABLE);

  if (the_obj)
    {
      dtype = the_obj->getDataType ();
      if (dtype == NULL)
        return true;
      VObjectType type = dtype->getType ();
      DataType* def = dtype->getDefinition ();

      if (type == VObjectType::slClass_declaration)
        {
          validFunction = checkValidFunction (dtype, function, stmt, design, datatypeName);
        }
      else if (dtype->isNumber (type) || dtype->isInteger_type (type) ||
               dtype->isNon_integer_type (type) || dtype->isString_type (type))
        {
          if (def)
            {
              type = def->getType ();
              dtype = def;
            }

          NodeId range = the_obj->getRange ();
          if (range)
            {
              VObjectType rangeType = the_obj->getFileContent ()->Type (range);

              if (rangeType == VObjectType::slUnsized_dimension)
                {
                  // Vector
                  validFunction = checkValidBuiltinClass_("array", function, stmt, design, datatypeName);
                }
              else if (rangeType == VObjectType::slVariable_dimension)
                {
                  FileContent* sfC = the_obj->getFileContent ();
                  NodeId subRange = sfC->Child (range);
                  VObjectType the_type = sfC->Type (subRange);
                  if (the_type == VObjectType::slQueue_dimension)
                    {
                      // Queue   

                      // foreach (darray[id]) darray[id].func() 
                      NodeId tmp = stmt->getNodeId ();
                      tmp = sfC->Child (tmp);
                      tmp = sfC->Sibling (tmp);
                      VObjectType t = sfC->Type (tmp);
                      if ((t == VObjectType::slConstant_bit_select) && sfC->Child (tmp))
                        {
                          // there is an actual array index 
                          if (type == VObjectType::slClass_declaration)
                            {
                              validFunction = checkValidFunction (dtype, function, stmt, design, datatypeName);
                            }
                        }
                      else
                        {
                          validFunction = checkValidBuiltinClass_("queue", function, stmt, design, datatypeName);
                        }
                    }
                  else if (the_type == VObjectType::slUnpacked_dimension)
                    {
                      // foreach (darray[id]) darray[id].func() 
                      NodeId subroutine_call = stmt->getNodeId ();
                      NodeId var_id = sfC->Child (subroutine_call);
                      NodeId constant_bit_select = sfC->Sibling (var_id);
                      VObjectType t = sfC->Type (constant_bit_select);
                      NodeId select_id = sfC->Child (constant_bit_select);
                      if ((t == VObjectType::slConstant_bit_select) && select_id)
                        {
                          validFunction = checkValidFunction (dtype, function, stmt, design, datatypeName);
                        }
                      else
                        {
                          validFunction = checkValidBuiltinClass_("queue", function, stmt, design, datatypeName);
                        }
                    }
                }
            }
          else
            {
              validFunction = checkValidFunction (dtype, function, stmt, design, datatypeName);
            }
        }
    }
  if (var_chain.size () == 0)
    {
      if (st->isSystemCall ())
        {
          validFunction = checkValidBuiltinClass_("system", function, stmt, design, datatypeName);
          if (!validFunction)
            { 
              FileContent* fC = st->getFileContent ();
              NodeId p = st->getNodeId ();
              std::string fileName = fC->getFileName (p);
              unsigned int line = fC->Line (p);
              Location loc1 (symbols->registerSymbol (fileName), line, 0, symbols->registerSymbol (function));
              Error err1 (ErrorDefinition::COMP_UNDEFINED_SYSTEM_FUNCTION, loc1);
              errors->addError (err1);
              return true;
            }
        }
      else
        {
          Function* func = classDefinition->getFunction (function);
          if (func)
            stmt->setFunction (func);
          else
            {
              validFunction = false;
              dtype = classDefinition;
            }
        }
    }

  if (validFunction == false)
    {
      if (dtype->isParameter ())
        {
          return true;
        }
      std::string name;
      for (auto v : var_chain) name += v + ".";
      if (name.size ())
        name = name.substr (0, name.size () - 1);
      while (dtype && dtype->getDefinition ())
        {
          dtype = dtype->getDefinition ();
        }
      if (name == "")
        {
          name = "this";
        }
      std::string typeName = dtype->getName ();
      if (datatypeName != "")
        typeName = datatypeName;
      NodeId p = st->getNodeId ();
      FileContent* fC = st->getFileContent ();
      std::string fileName = fC->getFileName (p);
      unsigned int line = fC->Line (p);
      Location loc1 (symbols->registerSymbol (fileName), line, 0, symbols->registerSymbol ("\"" + name + "\"" + " of type " + typeName));
      FileContent* fC2 = dtype->getFileContent ();
      std::string fileName2 = fC2->getFileName (dtype->getNodeId ());
      unsigned int line2 = fC2->Line (dtype->getNodeId ());
      Location loc2 (symbols->registerSymbol (fileName2), line2, 0, symbols->registerSymbol (function));
      Error err1 (ErrorDefinition::COMP_NO_METHOD_FOR_TYPE, loc1, loc2);
      errors->addError (err1);
    }
  return true;
}


bool TestbenchElaboration::bindForLoop_(ClassDefinition* classDefinition, Statement* stmt, ForLoopStmt* st) {
  FileContent* sfC = st->getFileContent ();
  NodeId fid = st->getNodeId ();
  VObjectType itr_type = st->getIteratorType (); 
  DataType* itrDataType = new DataType (sfC, fid, "integer", itr_type);
  for (auto itrId : st->getIteratorIds ())
    {
      Variable* var = new Variable (itrDataType, sfC, itrId.first, 0, sfC->SymName (itrId.first));
      st->getParentScope ()->addVariable (var);
    }
  return true;
}

bool TestbenchElaboration::bindForeachLoop_(ClassDefinition* classDefinition, Statement* stmt, ForeachLoopStmt* st) {

  NodeId arrayId = st->getArrayId ();
  FileContent* sfC = st->getFileContent ();
  std::vector<std::string> var_chain;
  computeVarChain (sfC, arrayId, var_chain);
  Variable* arrayVar = locateVariable_ (var_chain, sfC, arrayId, stmt->getScope (), classDefinition, ErrorDefinition::ELAB_UNDEF_VARIABLE);
  if (arrayVar)
    {
      NodeId range = arrayVar->getRange ();
      NodeId rangeTypeId = range;
      DataType* itrDataType = NULL;
      while (range)
        {
          rangeTypeId = range;
          range = sfC->Child (rangeTypeId);
        }
      VObjectType rangeType = sfC->Type (rangeTypeId);
      if (rangeType == VObjectType::slStringConst)
        {
          std::string dataTypeName = sfC->SymName (rangeTypeId);
          itrDataType = bindDataType_ (dataTypeName, sfC, rangeTypeId,
                                       classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
        }
      else if (rangeType == VObjectType::slAssociative_dimension ||
               rangeType == VObjectType::slQueue_dimension)
        {
          // Integer Type
          itrDataType = new DataType (sfC, arrayId, "integer", VObjectType::slIntegerAtomType_Int);
        }

      for (auto itrId : st->getIteratorIds ())
        {
          Variable* var = new Variable (itrDataType, sfC, itrId, 0, sfC->SymName (itrId));
          st->getParentScope ()->addVariable (var);
        }
    }
  return true;
}

bool TestbenchElaboration::bindFunctionBodies_() {
  Compiler* compiler = m_compileDesign->getCompiler ();
  ErrorContainer* errors = compiler->getErrorContainer ();
  SymbolTable* symbols = compiler->getSymbolTable ();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions ();  
  
   // Bind Function return values, parameters and body
   for (ClassNameClassDefinitionMultiMap::iterator itr = classes.begin(); itr != classes.end(); itr++)
    {
      std::string className = (*itr).first;
      ClassDefinition* classDefinition = (*itr).second;
      for (auto& func : classDefinition->getFunctionMap ())
        {
          // Skip binding of parameterized classes
          if (!classDefinition->hasCompleteBaseSpecification ())
            continue;

          std::queue<Statement*> stmts;
          for (Statement* stmt : func.second->getStmts ())
            stmts.push (stmt);
          
          while (stmts.size())
            {
              Statement* stmt = stmts.front ();
              stmts.pop();
              for (Statement* stmt1 : stmt->getStatements())
                stmts.push (stmt1);
              VObjectType stmt_type = stmt->getType();
              switch (stmt_type)
                {
                case VObjectType::slPs_or_hierarchical_array_identifier:
                  {
                    // Foreach loop
                    ForeachLoopStmt* st = dynamic_cast<ForeachLoopStmt*> (stmt);
                    if (st)
                      {
                        bindForeachLoop_(classDefinition, stmt, st);
                      }
                    break;
                  }
                case VObjectType::slFor_initialization:
                {
                    // For loop
                    ForLoopStmt* st = dynamic_cast<ForLoopStmt*> (stmt);
                    if (st)
                      {
                        bindForLoop_(classDefinition, stmt, st);
                      }
                    break;
                }
                case VObjectType::slSubroutine_call_statement:
                    bindSubRoutineCall_(classDefinition, stmt, design, symbols, errors);
                    break;                 
                default:
                  break;
                }
            }
        }
     }
  return true;
}

bool TestbenchElaboration::bindTasks_() {
  Compiler* compiler = m_compileDesign->getCompiler ();
  //ErrorContainer* errors = compiler->getErrorContainer ();
  //SymbolTable* symbols = compiler->getSymbolTable ();
  Design* design = compiler->getDesign();
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions ();  
   
   // Bind Tasks parameters and body
   for (ClassNameClassDefinitionMultiMap::iterator itr = classes.begin(); itr != classes.end(); itr++)
     {
      std::string className = (*itr).first;
      ClassDefinition* classDefinition = (*itr).second;
  
      // Bind Tasks parameters
      for (auto& func : classDefinition->getTaskMap ())
        {
          for (auto param : func.second->getParams ())
            {
              DataType* dtype = param->getDataType ();
              std::string dataTypeName = dtype->getName ();
              if (dtype->getDefinition ())
                continue;
              if (dtype->getFileContent () == NULL)
                continue;
              if (dtype->getType () == VObjectType::slStringConst)
                {
                  DataType* the_def = bindDataType_ (dataTypeName, dtype->getFileContent (), param->getNodeId (),
                                                     classDefinition, ErrorDefinition::COMP_UNDEFINED_TYPE);
                  if (the_def != dtype)
                    dtype->setDefinition (the_def);
                }
            }
        }
     }
  return true;
}

