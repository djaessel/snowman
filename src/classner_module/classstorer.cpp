#include "classstorer.h"

static bool ClassStorerInit = false;


ClassStorer::ClassStorer(Structer structer, vector<RawClass> classList)
{
  if (!ClassStorerInit)
    ClassStorer::initValues();

  this->classList = classList;
  this->structer = structer;
}

void ClassStorer::initValues()
{
  ClassStorerInit = true;

  ClassStorer::ExportDir = QString("generated_classes");

  ClassStorer::ParamTypes = map<QString, QString>();
  ClassStorer::ParamTypes.insert_or_assign(QString("i"), QString("int32_t"));
  ClassStorer::ParamTypes.insert_or_assign(QString("v"), QString("void")); // no parameters
  ClassStorer::ParamTypes.insert_or_assign(QString("b"), QString("bool"));
  ClassStorer::ParamTypes.insert_or_assign(QString("Kb"), QString("const bool")); // const
  ClassStorer::ParamTypes.insert_or_assign(QString("RKb"), QString("const bool &")); // by reference const
  // when RK<d> --> RK4Item... --> "const Item &"

  ClassStorer::ParamAsmNames = QStringList();
  // "rdi", // skip first, is always class object pointer -> this
  ClassStorer::ParamAsmNames.append(QString("rsi"));
  ClassStorer::ParamAsmNames.append(QString("rdx"));
  ClassStorer::ParamAsmNames.append(QString("rcx"));
  ClassStorer::ParamAsmNames.append(QString("r8"));
  ClassStorer::ParamAsmNames.append(QString("r9"));
  ClassStorer::ParamAsmNames.append(QString("a<x>"));

  ClassStorer::Replaces = map<QString, QString>();
  // replace LLVM 1-Bit values with boolean
  ClassStorer::Replaces.insert_or_assign(QString(" uint1_t"), QString(" bool"));
  ClassStorer::Replaces.insert_or_assign(QString(" int1_t"), QString(" bool"));
  // ---
  ClassStorer::Replaces.insert_or_assign(QString(" unsigned char"), QString(" BYTE"));
  ClassStorer::Replaces.insert_or_assign(QString(" signed char"), QString(" S_BYTE"));
  // return_address() from Decompiler GCC replacement(?)
  ClassStorer::Replaces.insert_or_assign(QString("__return_address()"), QString("__builtin_extract_return_addr(__builtin_return_address(0))"));
  // __zero_stack_offset() from Decompiler GCC replacement(?)
  ClassStorer::Replaces.insert_or_assign(QString("__zero_stack_offset()"), QString("zero_stack_offset()"));

  ClassStorer::AllValidTypes = QStringList()
      << QString("void") << QString("void*") << QString("void**") << QString("void***")
      << QString("bool") << QString("bool*") << QString("bool**") << QString("bool***")
      << QString("int8_t") << QString("int8_t*") << QString("int8_t**") << QString("int8_t***")
      << QString("uint8_t") << QString("uint8_t*") << QString("uint8_t**") << QString("uint8_t***")
      << QString("int16_t") << QString("int16_t*") << QString("int16_t**") << QString("int16_t***")
      << QString("uint16_t") << QString("uint16_t*") << QString("uint16_t**") << QString("uint16_t***")
      << QString("int32_t") << QString("int32_t*") << QString("int32_t**") << QString("int32_t***")
      << QString("uint32_t") << QString("uint32_t*") << QString("uint32_t**") << QString("uint32_t***")
      << QString("int") << QString("int*") << QString("int**") << QString("int***")
      << QString("uint") << QString("uint*") << QString("uint**") << QString("uint***")
      << QString("int64_t") << QString("int64_t*") << QString("int64_t**") << QString("int64_t***")
      << QString("uint64_t") << QString("uint64_t*") << QString("uint64_t**") << QString("uint64_t***")
      << QString("char") << QString("char*") << QString("char**") << QString("char***")
  //    << QString("signed char") << QString("signed char*") << QString("signed char**") << QString("signed char***")
      << QString("BYTE") << QString("BYTE*") << QString("BYTE**") << QString("BYTE***")
      << QString("S_BYTE") << QString("S_BYTE*") << QString("S_BYTE**") << QString("S_BYTE***")
      << QString("float") << QString("float*") << QString("float**") << QString("float***")
      << QString("double") << QString("double*") << QString("double**") << QString("double***")
  ;

  ClassStorer::AllValidSpecialTypes = QStringList()
      << QString("struct") << QString("struct*") << QString("struct**") << QString("struct***")
      // are there more ???
  ;
}

void ClassStorer::writeClassHeaderFile(RawClass cls)
{
#if DEBUGMODE
  cout << "  Writing " << cls.getName().toStdString().c_str() << " class header...";
#endif

  QFile file(ClassStorer::ExportDir + QString("/") + cls.getName() + QString(".h"));
  if(!file.open(QIODevice::WriteOnly)) {
      cout << "CLASSSTORER 1 ERROR: File could not be opened - " << cls.getName().toStdString().c_str() << ".h" << endl;
  }

  QTextStream out(&file);
  out << "#ifndef " << cls.getName().toUpper().toStdString().c_str() << "_H" << "\n";
  out << "#define " << cls.getName().toUpper().toStdString().c_str() << "_H" << "\n";
  out << "\n";
  out << "#include <inttypes.h>\n";
  out << "#include <iostream>\n";
  out << "#include <stddef.h>\n";
  out << "#include <boost/multiprecision/cpp_int.hpp>\n";
  out << "#include <string>\n"; // maybe add more later on (e.g. used classes)
  out << "\n";
  out << "/* CUSTOM INCLUDES */\n";
  out << "#include \"snowmany.h\"\n";
  out << "\n";
  out << "/* GENERATED INCLUDES */\n";
  out << "// USED_CLASSES" << "\n"; // will be replaced with includes
  out << "\n";
  out << "\n";
  out << "// STRUCTS_GEN" << "\n"; // to be replaced by structs later
  out << "\n";
  out << "class " << cls.getName().toStdString().c_str() << "\n";
  out << "{" << "\n";
  out << "public:" << "\n";
  //out << "  " << cls.getName().toStdString().c_str() << "() {}" << "\n"; # write empty constructor if nothing found - later check for depending object calls etc

  foreach (RawFunction func, cls.getFunctions()) {
      QString returnType = "void"; // void until proven otherwise
      QString cppFileFuncName = this->classFunctionParameterFix(func.getDeclar(), func.getMangledName()); // make with actual parameters
      out << "  " << returnType.toStdString().c_str() << " " << cppFileFuncName.toStdString().c_str() << "; // " << func.getMangledName() << " " << Qt::endl;
  }

  out << "};" << "\n";
  out << "\n";
  out << "#endif // " << cls.getName().toUpper().toStdString().c_str() << "_H" << "\n";
  out << "\n";

  file.close();

#if DEBUGMODE
  cout << "DONE" << endl;
#endif
}

void ClassStorer::writeClassesJust(map<QString, FixedClass> fixedClasses, map<QString, QStringList> classIncludes)
{
  if (!QDir(ClassStorer::ExportDir).exists())
    QDir().mkdir(ClassStorer::ExportDir);

  cout << "WRITING FIXED CLASSES BEGIN" << endl;

  foreach (auto cls, fixedClasses) {
      QStringList startLines;
      QStringList myFuncs;

      QString fileP(ClassStorer::ExportDir + "/" + cls.first + ".cpp");
      QFile file(fileP);
      if(!file.open(QIODevice::ReadOnly)) {
          cout << "CLASSSTORER 2 ERROR: File could not be opened - " << fileP.toStdString().c_str() << endl;
      }

      bool molMode = false;
      QTextStream in(&file);
      while(!in.atEnd()) {
          QString line = in.readLine();
          if (line.contains(cls.first + "::")){
              myFuncs.append(line);
              molMode = true;
          }

          if (!molMode)
            startLines.append(line);
      }
      file.close();

      QFile file2(fileP);
      if(!file2.open(QIODevice::WriteOnly)) {
          cout << "CLASSSTORER 3 ERROR: File could not be opened - " << fileP.toStdString().c_str() << endl;
      }

      QTextStream out(&file2);
      foreach (QString line, startLines) {
          out << line.toStdString().c_str() << Qt::endl;
      }

      foreach (FixedFunction func, fixedClasses[cls.first].getFunctions()) {
          foreach (QString fun, myFuncs) {
              if (fun.contains("::" + func.getName() + "(")){
                  out << fun.toStdString().c_str() << Qt::endl; // write func head
                  break;
              }
          }

          foreach (QString line, func.getCodeLines()) {
              out << line.toStdString().c_str() << Qt::endl;
          }

          out << "\n\n\n";
      }
      file2.close();

      QStringList allLinesX;
      QString fileP3(ClassStorer::ExportDir + "/" + cls.first + ".h");
      QFile file3(fileP3);
      if(!file3.open(QIODevice::ReadOnly)) {
          cout << "CLASSSTORER 4 ERROR: File could not be opened - " << fileP3.toStdString().c_str() << endl;
      }

      QTextStream in2(&file3);
      while(!in2.atEnd()) {
          QString line = in2.readLine();
          if (line.contains("// USED_CLASSES")) {
              line = "";
              foreach (QString include, classIncludes[cls.first])
                  line += "#include \"" + include + ".h\"\n";
              line += "\n";
          }
          allLinesX.append(line);
      }
      file3.close();

      QFile file4(fileP3);
      if(!file4.open(QIODevice::WriteOnly)) {
          cout << "CLASSSTORER 5 ERROR: File could not be opened - " << fileP3.toStdString().c_str() << endl;
      }

      QTextStream out2(&file4);
      foreach (QString line, allLinesX) {
          out2 << line.remove(QRegExp("([\n]$)")).toStdString().c_str() << Qt::endl;
      }
      file4.close();
  }

  cout << "WRITING FIXED CLASSES END" << endl << endl;
}

QString ClassStorer::replaceSymbolsInLine(QString line)
{
  foreach (auto repl, ClassStorer::Replaces) {
      line = line.replace(repl.first, repl.second);
  }

  QString tmp = nullptr;
  bool decl = false;
  bool commax = false;

  QString operx("operator");

  while (line.contains("_Z") && tmp != line) {
      tmp = QString(line);
      QString cutty = line.right(line.size() - line.indexOf("_Z"));

      if (cutty.indexOf("(") >= 0){
        cutty = cutty.left(cutty.indexOf("("));
      } else if (cutty.indexOf(")") >= 0){
        cutty = cutty.left(cutty.indexOf(")"));
        decl = true;
      } else if (cutty.indexOf(";") >= 0) {
        cutty = cutty.left(cutty.indexOf(";"));
        commax = true;
      } else {
          cout << "ERROR" << endl;
      }

      if (this->allFuncs.find(cutty) != this->allFuncs.end()) {
          if (this->allFuncs[cutty].contains(operx)) {
              QString lem = this->allFuncs[cutty];
              QString curOperator = lem.right(lem.size() - (lem.indexOf(operx) + operx.size()));
              curOperator = curOperator.left(curOperator.indexOf("(")); // FIXME: make correct operator handling!

              QString sectox = lem.split("(")[1].split(")")[0];
              QStringList secto = sectox.split(',');

              QString curClsName = this->allFuncClass[cutty];
              if (commax || decl) {
                  line = line.replace(cutty + "(" + sectox + ")", curClsName + "(UNKNOWN_OBJECT_RDI_1) " + curOperator + " " + curClsName + "(" + secto.back() + ")");
              } else {
                  QString los, molto;
                  QString rdix = line.right(line.size() - line.indexOf(cutty));
                  if (rdix.indexOf(",") >= 0) {
                      rdix = rdix.left(rdix.indexOf(","));
                      if (rdix.indexOf("(") >= 0)
                        rdix = rdix.split("(")[1];
                      los = rdix + ", ";
                      molto = "";
                      // ...
                  } else if (rdix.indexOf(")") >= 0) {
                      rdix = rdix.left(rdix.indexOf(")"));
                      if (rdix.indexOf("(") >= 0)
                        rdix = rdix.split("(")[1];
                      los = "(" + rdix + ")";
                      molto = "()";
                      // ...
                  }

                  rdix = rdix.trimmed();
                  if (rdix.size() <= 0) {
                      rdix = "UNKNOWN_OBJECT_RDI_2";
                  }

                  QString solom = line.right(line.size() - line.indexOf(cutty));
                  solom = solom.right(solom.size() - solom.indexOf("("));

                  int clam = 0;
                  int iid = -1;
                  bool charActive = false;

                  for (int i = 0; i < solom.size(); i++) {
                      if (!charActive && solom[i] == '(')
                        clam++;
                      else if (!charActive && solom[i] == ')')
                        clam--;
                      else if (solom[i] == '"' && i > 0 &&
                               (solom[i - 1] != '\\' || (solom[i - 1] == '\\' && i > 1 && solom[i - 2] == '\\'))) // only actual string start and end characters should count
                        charActive = !charActive;

                      if (clam <= 0) {
                          iid = i;
                          break;
                      }
                  }

                  int endo = 0;
                  if (iid >= 0) {
                      solom = solom.left(iid) + ")";
                      secto = solom.split(',');
                      endo = min(1, secto.size() - 1);
                  } else {
                      cout << "ERROR " << solom.toStdString().c_str() << " " << line.toStdString().c_str() << endl;
                  }

                  line = line.replace(
                    cutty + solom,
                    curClsName + "(" + rdix + ") " + curOperator + " " + curClsName + "(" + secto[endo].remove(QRegExp("^([ ]+)")).remove(QRegExp("([)]+)$")) + ")"
                  ).remove(QRegExp("([\n]+)$")) + " // remove rdi val and set as proper object\n";


              }
          } else {
              if (commax || decl) {
                  line = line.replace(cutty, "UNKNOWN_OBJECT_RDI_1->" + this->allFuncs[cutty].split("(")[0]) + " // find rdi val and set as proper object";
              } else { // FIXME: change the rdix code to work correctly or not use it at all!
                  QString los, molto;
                  QString rdix = line.right(line.size() - line.indexOf(cutty));
                  if (rdix.indexOf(",") >= 0) {
                      rdix = rdix.left(rdix.indexOf(","));
                      if (rdix.indexOf("(") >= 0)
                        rdix = rdix.split("(")[1];
                      los = rdix + ", ";
                      molto = "";
                      rdix = rdix.split(' ').back();
                  } else if (rdix.indexOf(")") >= 0) {
                      rdix = rdix.left(rdix.indexOf(")"));
                      if (rdix.indexOf("(") >= 0)
                        rdix = rdix.split("(")[1];
                      los = "(" + rdix + ")";
                      molto = "()";
                      rdix = rdix.split(' ').back();
                  }

                  rdix = rdix.trimmed();
                  if (rdix.length() <= 0) {
                      rdix = "UNKNOWN_OBJECT_RDI_2";
                  }

                  line = line.replace(cutty, rdix + "->" + this->allFuncs[cutty].split("(")[0]).replace(los, molto) + " // remove rdi val and set as proper object";
              }
          }
      }
  }

  return line;
}

QString ClassStorer::classFunctionParameterFix(QString fname, QString assemblyFuncName)
{
  if (fname.indexOf("(") < 0) {
#if DEBUGMODE
  #if SPECIAL_DEBUG
      cout << "classFunctionParameterFix : " << fname.toStdString().c_str() << " : " << assemblyFuncName.toStdString().c_str() << endl;
  #endif
#endif
      fname = assemblyFuncName; // FIXME: temporary fix?
  } else {
      QStringList telp = fname.split("(")[1].split(")")[0].split(',');
      fname = fname.split("(")[0] + "("; // base name without parameters

      if (telp.length() > 1 || telp[0].length() > 0) {
          QStringList parax = assemblyFuncName.split("(")[1].split(")")[0].split(",");
          for (int i = 0; i < telp.length(); i++) {
              QString lasx = nullptr;

              if (parax.length() > (i + 1)) {
                  QStringList lasxList = parax[i + 1].split(' ');
                  if (lasxList.length() > 0)
                    lasx = lasxList.back();
              } // else FIXME: bug with sometimes missing parameters mentioned in assembly func name!!!

              int idx = i - 1;
              if (idx >= ClassStorer::ParamAsmNames.length())
                idx = ClassStorer::ParamAsmNames.length() - 1;

              if (idx < 0) // this was not in the original, but there is a bug with INDEX!!!
                idx = ClassStorer::ParamAsmNames.length() - 1; // idx = 0;

              QString nox = ClassStorer::ParamAsmNames[idx].replace("<x>", QString(i));
              if (lasx != nullptr && lasx != nox)
                nox = lasx;

              fname += telp[i] + " " + nox + ",";
          }
      }

      fname = fname.remove(QRegExp(R"(([,]+)$)")) + ")";
  }

  return fname;
}

void ClassStorer::updateNewCppFile(QString filePath/*, vector<RawClass> classes*/)
{
  cout << "Update cleaned cpp file...";

  QStringList pathArray = filePath.split('/');
  QString fileName = pathArray.back();

  QFile file(ClassStorer::ExportDir + QString("/") + fileName);
  if(!file.open(QIODevice::ReadOnly)) {
      cout << "CLASSSTORER 6 ERROR: File could not be opened - " << fileName.toStdString().c_str() << endl;
  }

  QTextStream in(&file);
  QStringList lines;
  while (!in.atEnd()) {
      lines.append(in.readLine());
  }
  file.close();

  QFile file2(ClassStorer::ExportDir + QString("/") + fileName);
  if(!file2.open(QIODevice::WriteOnly)) {
      cout << "CLASSSTORER 7 ERROR: File could not be opened - " << fileName.toStdString().c_str() << endl;
  }

  QTextStream out(&file2);
  foreach (QString line, lines) {
      line = this->replaceSymbolsInLine(line);
      line = line.remove(QRegExp(R"([\n]+$)"));
      out << line.toStdString().c_str() << "\n";
  }
  file2.close();

  cout << "DONE" << endl;
}

void ClassStorer::writeClassCodeFile(RawClass cls)
{
#if DEBUGMODE
  cout << "  Writing " << cls.getName().toStdString().c_str() << " class functions...";
#endif

  QFile file(ClassStorer::ExportDir + QString("/") + cls.getName() + QString(".cpp"));
  if(!file.open(QIODevice::WriteOnly)) {
      cout << "CLASSSTORER 8 ERROR: File could not be opened - " << cls.getName().toStdString().c_str() << ".cpp" << endl;
  }

  QTextStream out(&file);
  out << "#include \"" << cls.getName().toStdString().c_str() << ".h\"" << "\n";
  out << "\n";

  auto structs = this->structer.getStructs();

  foreach (RawFunction func, cls.getFunctions()) {
      map<QString, QString> variables;

      QString returnType = "void"; // void until proven otherwise
      QString cppFileFuncName = this->classFunctionParameterFix(func.getDeclar(), func.getMangledName()); // make with actual parameters

      out << returnType.toStdString().c_str() << " " << cls.getName().toStdString().c_str() << "::" << cppFileFuncName.toStdString().c_str() << "\n"; // add return value and maybe basic parameter names

      map<QString, QString> usedAsPointer;
      //map<QString, int> toBeDeleted;
      vector<int> toBeDeleted;

      int max = func.getCodeLines().size();
      for (int i = 0; i < max; i++) {
          QString line = func.getCodeLine(i);
          QString monline = line.remove(QRegExp("([\n]+)$")).remove(QRegExp("([;]+)$")).trimmed();

          foreach (auto pair, ClassStorer::Replaces) {
              monline = monline.replace(pair.first, pair.second);
          }

          QStringList monem = monline.split(' ');
          if (monem.size() == 2) {
              if (ClassStorer::AllValidTypes.contains(monem[0])) {
                  variables.insert_or_assign(monem[1], monem[0]);
                  //toBeDeleted.insert_or_assign(monem[1], i);
                  toBeDeleted.insert(toBeDeleted.begin(), i);
              } // else not valid
          } else if (monem.size() == 3) {
              if (ClassStorer::AllValidSpecialTypes.contains(monem[0])) {
                  variables.insert_or_assign(monem[2], "STRUCT_" + monem[1].right(monem[1].size() - 1)); // change later to meaningful name or fix
                  //toBeDeleted.insert_or_assign(monem[2], i);
                  toBeDeleted.insert(toBeDeleted.begin(), i);
              } // else not valid
          }
      }

      foreach (int idx, toBeDeleted) {
          func.removeCodeLine(idx);
      }

      if (func.getCodeLines().size() > 0 && func.getCodeLine(0).trimmed().size() == 0) {
          func.removeCodeLine(0);
      }

      out << "{\n";

      foreach (QString line, func.getCodeLines()) {
          line = this->replaceSymbolsInLine(line);

          foreach (auto varx, variables) {
              if (line.contains(varx.first) && !line.contains(varx.first + " =")) {
                  if ((line.contains("(" + varx.first) && line.contains(varx.first + ",")) ||
                      line.contains(" " + varx.first + ",") ||
                      line.contains(varx.first + ")") ||
                      line.contains(varx.first + " +") ||
                      line.contains(varx.first + " -") ||
                      line.contains(varx.first + " *")
                      ) {
                      usedAsPointer.insert_or_assign(varx.first, varx.second);
                  }
              }
          }

          foreach (auto uap, usedAsPointer) {
              if (variables.find(uap.first) != variables.end()) {
                  variables.erase(uap.first);
              }
          }

          if (line.contains("=")) {
              QString tmpp = line.split("=")[0].remove(QRegExp("^([ \t]+)"));
              QString foundVar = nullptr;
              foreach (auto varx, variables) {
                  if (tmpp.contains(varx.first + " ") && tmpp.indexOf(varx.first) == 0 && line.indexOf(varx.first) <= 4) {
                      line = line.replace(varx.first + " =", varx.second + " " + varx.first + " =");
                      foundVar = varx.first;
                  }
              }

              if (foundVar != nullptr) {
                  variables.erase(foundVar);
              }
          }

          if (line.contains("struct")) { // replace structs in code with "actual" name
              foreach (auto structx, structs) {
                  QString tetraTmp = "struct " + QString(structx.first).replace("STRUCT_", "s");
                  if (line.contains(tetraTmp)) {
                      if (line.contains(tetraTmp + " "))
                          line = line.replace(tetraTmp + " ", structx.first + " ");
                      if (line.contains(tetraTmp + "***"))
                          line = line.replace(tetraTmp + "***", structx.first + "***");
                      if (line.contains(tetraTmp + "**"))
                          line = line.replace(tetraTmp + "**", structx.first + "**");
                      if (line.contains(tetraTmp + "*"))
                          line = line.replace(tetraTmp + "*", structx.first + "*");
                  }
              }
          }

          out << line.toStdString().c_str() << "\n";
      }

      if (usedAsPointer.size() > 0) {
          out << "  // possible pointer usage or inline declarations" << "\n";
          foreach (auto uap, usedAsPointer) {
              out << "  // " << uap.second.toStdString().c_str() << " " << uap.first.toStdString().c_str() << "\n";
          }
      }

      out << "}\n\n\n";
  }
  file.close();

#if DEBUGMODE
  cout << "DONE" << endl;
#endif
}

void ClassStorer::writeClasses()
{
  if (!QDir(ClassStorer::ExportDir).exists())
    QDir().mkdir(ClassStorer::ExportDir);

  this->allFuncs.clear();
  this->allFuncClass.clear();

  QString folyr;
  QStringList foly;
  foreach (RawClass cls, this->classList) {
      foreach (RawFunction func, cls.getFunctions()) {
          folyr = nullptr;
          foly = func.getMangledName().split(' ');
          foreach (QString ll, foly) {
              if (ll.indexOf("_Z") == 0) {
                  folyr = ll.split("(")[0];
                  break;
              }
          }

          if (folyr != nullptr) {
              this->allFuncs.insert_or_assign(folyr, func.getDeclar().trimmed());
              this->allFuncClass.insert_or_assign(folyr, cls.getName());
          }
      }
  }

#if DEBUGMODE
  cout << "WRITING CLASSES BEGIN" << endl;
#else
  cout << "Writing classes...";
  cout.flush();
#endif

  uint processor_count = processorCount();
  int length = this->classList.size() / processor_count;
  for (uint i = 0; i < processor_count; i++) {
      int start = i * length;
      int end = start + length;
      if (i == processor_count - 1)
          end = this->classList.size();

      ClassStorerTask *hello = new ClassStorerTask(this, &this->classList, start, end);
      // QThreadPool takes ownership and deletes 'hello' automatically
      QThreadPool::globalInstance()->start(hello);
  }
  QThreadPool::globalInstance()->waitForDone(); // waits for all to be done(?)

  //foreach (RawClass cls, this->classList) {
  //    this->writeClassHeaderFile(cls);
  //    this->writeClassCodeFile(cls);
  //    this->writeStructsForHeader(cls);
  //}

#if DEBUGMODE
  cout << "WRITING CLASSES END" << endl << endl;
#else
  cout << "DONE" << endl;
#endif
}

void ClassStorer::writeStructsForHeader(RawClass cls)
{
  map<QString, QStringList> structs = this->structer.getStructs();

#if DEBUGMODE
  cout << "  Writing " << cls.getName().toStdString().c_str() << " class used structs...";
#endif

  QFile file(ClassStorer::ExportDir + QString("/") + cls.getName() + QString(".cpp"));
  if(!file.open(QIODevice::ReadOnly)) {
      cout << "CLASSSTORER 9 ERROR: File could not be opened - " << cls.getName().toStdString().c_str() << ".cpp" << endl;
  }

  QString allCode;
  QTextStream in(&file);
  while (!in.atEnd()) {
      allCode = in.readAll();
  }
  file.close();

  QFile file2(ClassStorer::ExportDir + QString("/") + cls.getName() + QString(".h"));
  if(!file2.open(QIODevice::ReadOnly)) {
      cout << "CLASSSTORER 10 ERROR: File could not be opened - " << cls.getName().toStdString().c_str() << ".h" << endl;
  }

  QString allHeader;
  QTextStream in2(&file2);
  while (!in2.atEnd()) {
      allHeader = in2.readAll();
  }
  file2.close();

  bool firstStruct = true;
  QString newStructCode("");
  foreach (auto structx, structs) {
      QString defStruct = QString(structx.first).replace("STRUCT_", "s");
      if (allCode.contains(defStruct) || allHeader.contains(defStruct)) {
          if (!firstStruct) {
              newStructCode += "\n";
          }
          foreach (QString line, structx.second) {
              newStructCode += line + "\n";
          }
          newStructCode += "\n";
          firstStruct = false;
      }
  }

  allHeader = allHeader.replace("// STRUCTS_GEN", newStructCode);

  QFile file3(ClassStorer::ExportDir + QString("/") + cls.getName() + QString(".h"));
  if(!file3.open(QIODevice::WriteOnly)) {
      cout << "CLASSSTORER 11 ERROR: File could not be opened - " << cls.getName().toStdString().c_str() << ".h" << endl;
  }

  QTextStream out(&file3);
  out << allHeader << Qt::endl;
  file3.close();

#if DEBUGMODE
  cout << "DONE" << endl;
#endif
}
