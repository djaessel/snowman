#include "classner.h"


Classner::Classner()
{
}

int Classner::indexOfClass(QString className)
{
  int index = -1;

  int curIdx = -1;
  foreach (RawClass ccc, this->classes) {
      curIdx++;
      if (ccc.getName() == className) {
          index = curIdx;
          break;
      }
  }

  return index;
}

bool Classner::classExists(QString className)
{
  bool exists = false;
  foreach (RawClass ccc, this->classes) {
      if (ccc.getName() == className) {
          exists = true;
          break;
      }
  }
  return exists;
}

void Classner::saveNewCppFile(QString filePath, QStringList linesToStore)
{
  cout << "Writing cleaned cpp file...";

  QDir exportDir(ClassStorer::ExportDir);
  if (!exportDir.exists()) {
      QDir().mkdir(exportDir.absolutePath());
  }

  QStringList pathArray = filePath.split("/");
  QString fileName = pathArray.back();

  QFile file(exportDir.absolutePath() + QString("/") + fileName);
  if(!file.open(QIODevice::WriteOnly)) {
      cout << "CLASSNER 1 ERROR: File could not be opened - " << filePath.toStdString().c_str() << endl;
  }

  QTextStream out(&file);
  foreach (QString line, linesToStore) {
      out << line.toStdString().c_str() << Qt::endl;
  }
  file.close();

  cout << "DONE" << endl;
}

void Classner::readClassFunctions(QString filePath, bool skipNewCpp)
{
  vector<RawFunction> classFunctions;
//  int lineIndex = -1;
  QStringList ignoredLines;

  cout << "Reading class functions...";

  QFile file(filePath);
  if(!file.open(QIODevice::ReadOnly)) {
      cout << "CLASSNER 2 ERROR: File could not be opened - " << filePath.toStdString().c_str() << endl;
  }

  bool nextIsDecl = false;
  bool classBody = false;

  // FIXME: a lot of classes and their functions are still not included
  // TODO: handle functions that have different names/class structures later!!! Do not forget!!!
  QRegExp regex1(R"([a-zA-Z0-9-_<>*]+::[~]*[a-zA-Z0-9-_<>*]+[ a-z]*[<>=&|^*+\/-~\(\)\[\]]*\([a-zA-Z,.<>:0-9-_& \*\(\)]*\))");
  QRegExp regex2(R"([a-zA-Z0-9-_<>*]+\([a-zA-Z,.<>:0-9-_& \*]*\))");
  QRegExp regex3(R"(_Z[a-zA-Z0-9-_]+\([a-zA-Z,.<>:0-9-_& \*]*\))");

  QTextStream in(&file);
  while(!in.atEnd()) {
      //lineIndex++;
      QString line = in.readLine().remove(QRegExp("([\n]{1})$"));

      if (nextIsDecl) {
          line = line.trimmed();
          if (line.contains(";")) {
              classFunctions.pop_back();
          } else {
              classFunctions.back().setMangledName(line);
              classBody = true;
          }

          nextIsDecl = false;
      } else if (classBody) {
          if (line == QString("}")) {
              classBody = false;
          } else {
              classFunctions.back().addCodeLine(line);
          }
      } else if (line.startsWith("/*")) {
          line = line.trimmed();
          bool modo = false;

          if (line.endsWith("*/") && line.contains("::")) {
              QString tmpax(line);
              line = line.right(line.size() - 3);
              line = line.left(line.size() - 2);
              line = line.trimmed();

              //QString cap;
              if((regex1.indexIn(line, 0)) >= 0) {
                  //cap = regex1.cap(1).trimmed();
                  classFunctions.push_back(RawFunction(line));
                  nextIsDecl = true;
              } else {
                  line = tmpax;
              }
          }

          if ((modo || !line.contains("::")) && !nextIsDecl and line.endsWith("*/")) {
              line = line.right(line.size() - 3);
              line = line.left(line.size() - 2);
              line = line.trimmed();

              if((regex2.indexIn(line, 0)) >= 0) {
                  classFunctions.push_back(RawFunction(line));
                  nextIsDecl = true;
              }
          }
      } else if (line.contains("_Z") and !(line.contains(" while ") || line.contains(" if ") || line.contains(";")) && line.contains("(") && line.contains(")")) {
          if((regex3.indexIn(line, 0)) >= 0) {
              RawFunction newFunc(QString("NO_COMMENT"));
              newFunc.setMangledName(line);
              classFunctions.push_back(newFunc);
              classBody = true;
          }
      } else {
          ignoredLines.append(line + "\n");
      }
  }
  file.close();

  cout << "DONE" << endl;

  if (!skipNewCpp) {
      this->saveNewCppFile(filePath, ignoredLines);
  }

  this->sortFuncsIntoClasses(classFunctions);
}

void Classner::sortFuncsIntoClasses(vector<RawFunction> funcs)
{
  this->classes.clear();

  cout << "Sort functions into classes...";

  QRegExp regex1(R"([^<>]+[<>]+[^<>]+[<>]+[^<>]*)");

  QStringList tmpXX;
  QStringList ddd;
  QString tmpXXX;
  QString curDeclar;
  QString className;
  foreach (RawFunction func, funcs) {
      curDeclar = func.getDeclar();
      if (curDeclar.indexOf("::") < curDeclar.indexOf("(")) {
          ddd = curDeclar.split("::");
      } else {
          ddd = QStringList(curDeclar);
      }

      if (ddd.size() > 1) {
          tmpXXX = ddd[0].replace(", ",",").replace("< ","<").replace(" >",">");
          tmpXX = tmpXXX.split("<")[0].split(" ");

          int lenx = 0;
          if (ClassStorer::AllValidTypes.contains(tmpXX[0])) {
              lenx = 1;
          } else if (tmpXX[0] == QString("non-virtual") && curDeclar.contains("non-virtual thunk to ")) {
              lenx = 3;
          } else if (tmpXX[0] == QString("unsigned") && ClassStorer::AllValidTypes.contains(tmpXX[1])) {
              lenx = 2;
          }

          className = tmpXX[lenx];
          if (ddd.size() > 2) {
              continue; // skip any namespace functions - they are usually importable and not from the main proram
          }

          className = className.replace("non-virtual thunk to", "").trimmed();

          if((regex1.indexIn(className, 0)) >= 0) {
              continue; // skip weird class functions for now
          }

          if (!this->classExists(className))
              this->classes.push_back(RawClass(className));

          int classIndex = this->indexOfClass(className);
          RawFunction newFunc(ddd[1]);
          newFunc.setMangledName(func.getMangledName());
          newFunc.setCodeLines(func.getCodeLines());
          this->classes[classIndex].addFunction(newFunc);
      } else if (ddd.size() == 1) {// when no class func
          className = "DecompiledSpecialFuncs";
          if((regex1.indexIn(className, 0)) >= 0) {
              continue; // skip weird class functions for now
          }

          if (!this->classExists(className))
              this->classes.push_back(RawClass(className));

          int classIndex = this->indexOfClass(className);
          RawFunction newFunc(ddd[0]);
          newFunc.setMangledName(func.getMangledName());
          newFunc.setCodeLines(func.getCodeLines());
          this->classes[classIndex].addFunction(newFunc);
      }
  }

  cout << "DONE" << endl;
}
