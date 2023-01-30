#include "functionanalyzer.h"
#include "classstorer.h"


// make this easier - read file as a whole and simply regex over it!
map<QString, QStringList> FunctionAnalyzer::addUsedClassImports(map<QString, FixedClass> *classes, vector<RawClass> *rawClasses)
{
  map<QString, QStringList> includes;

  cout << "Add used class imports..." << endl;

  //foreach (auto cls, classes) {
  //    includes.insert_or_assign(cls.first, this->addUsedClassImports(cls.first, classes, rawClasses));
  //}

  uint processor_count = processorCount();
  int length = classes->size() / processor_count;
  for (uint i = 0; i < processor_count; i++) {
      int start = i * length;
      int end = start + length;
      if (i == processor_count - 1)
          end = classes->size();

      FunctionAnalyzerTask *hello = new FunctionAnalyzerTask(this, &includes, classes, rawClasses, start, end);
      // QThreadPool takes ownership and deletes 'hello' automatically
      QThreadPool::globalInstance()->start(hello);
  }
  QThreadPool::globalInstance()->waitForDone(); // waits for all to be done(?)

  cout << "DONE" << endl;

  return includes;
}

void FunctionAnalyzer::addUsedCLassImportsHelper(QStringList *includes, map<QString, FixedClass> *classes, QString line, bool sec)
{
  foreach (auto cls2, *classes) {
      if (line.contains(cls2.first) && !includes->contains(cls2.first)) {
          if (line.contains(" " + cls2.first + "*") || line.contains(" " + cls2.first + " ") ||
              (sec && (line.contains(" " + cls2.first + "("))) ||
              (!sec && (line.contains("(" + cls2.first + " ") || line.contains("(" + cls2.first + "*")))) {
              includes->append(cls2.first);
          }
      }
  }
}

// FIXME: bottleneck!!!
QStringList FunctionAnalyzer::addUsedClassImports(QString cls, map<QString, FixedClass> *classes, vector<RawClass> *rawClasses)
{
  QStringList includes;

  foreach (RawClass obj, *rawClasses) {
      if (obj.getName() == cls) { // only for current class(?)
        foreach (RawFunction rawFunc, obj.getFunctions()) {
          this->addUsedCLassImportsHelper(&includes, classes, rawFunc.getDeclar());
        }
        break;
      }
  }

  foreach (FixedFunction func, classes->at(cls).getFunctions()) {
      foreach (QString line, func.getCodeLines()) {
          this->addUsedCLassImportsHelper(&includes, classes, line, true);
      }
  }

  return includes;
}

map<QString, FixedClass> FunctionAnalyzer::findOriginalClass(map<QString, FixedClass> *classes)
{
  map<QString, FixedClass> fixedClasses;

//  foreach (auto cls, *classes) {
//      fixedClasses.insert_or_assign(cls.first, this->findOriginalClass(cls.first, classes));
//  }

  cout << "Find original classes..." << endl;

  uint processor_count = processorCount();
  int length = classes->size() / processor_count;
  for (uint i = 0; i < processor_count; i++) {
      int start = i * length;
      int end = start + length;
      if (i == processor_count - 1)
          end = classes->size();

      FunctionAnalyzerTask *hello = new FunctionAnalyzerTask(this, &fixedClasses, classes, start, end);
      // QThreadPool takes ownership and deletes 'hello' automatically
      QThreadPool::globalInstance()->start(hello);
  }
  QThreadPool::globalInstance()->waitForDone(); // waits for all to be done(?)

  cout << "DONE" << endl;

  return fixedClasses;
}

FixedClass FunctionAnalyzer::findOriginalClass(QString cls, map<QString, FixedClass> *classes)
{
  FixedClass fixedClass;
  map<QString, QString> tracerx;
  //bool foundSomething = false;

#if DEBUGMODE
  cout << "Analyzing " << cls.toStdString().c_str() << "...";
#endif

  foreach (FixedFunction func, classes->at(cls).getFunctions()) {
      FixedFunction fixedFunc(func.getName());
      bool declarMode = false;
      foreach (QString line, func.getCodeLines()) {
          if (line.contains("possible pointer usage or inline declarations")) declarMode = true;
          else if (declarMode) {
              if (!line.contains("}"))
                fixedFunc.insertCodeLine(1, line.replace("// ", "  ").remove("\n") + QString(";"));
              else
                fixedFunc.addCodeLine(line);
          } else {
              foreach (auto cls2, *classes) {
                  foreach (FixedFunction func2, cls2.second.getFunctions()) {
                      QString lll = "->" + func2.getName();
                      if (line.contains(lll)) {
                          bool skip = false;
                          foreach (auto trx, tracerx) {
                              if (line.contains(trx.first + lll)) {
                                  skip = true;
                                  break;
                              }
                          }

                          if (!skip && (line.contains(lll + "(") ||
                                        line.contains(lll + ";") ||
                                        line.contains(lll + ")"))) {
                              //if (!foundSomething) {
                              //    cout << cls.toStdString().c_str() << ": [fixing 1]" << endl;
                              //    foundSomething = true;
                              //}
                              //cout << "FOUND TRACE: " << cls2.first.toStdString().c_str() << " " << func2.getName().toStdString().c_str() << " " << line.toStdString().c_str();
                              int idx = line.indexOf(lll);
                              QStringList tmpx = line.left(idx).split(' ');
                              QString tmpx2("");
                              if (tmpx.length() > 0)
                                tmpx2 = tmpx.back();
                              tmpx2 = tmpx2.remove(QRegExp("^([&]+)")).remove(QRegExp("^([*]+)")); // remove extras # TODO: check again alter
                              QString func2Name = func2.getName();
                              if (classes->at(cls).getFunction(func2Name).getName() != nullptr) {
                                  line = line.replace(tmpx2 + "->" + func2Name, "this->" + func2Name);
                              } else if (tmpx2.length() > 0 && tracerx.count(tmpx2) <= 0) {
                                  tracerx.insert_or_assign(tmpx2, cls2.first);
                              } else {
                                  cout << cls2.first.toStdString().c_str() << " > ERROR: EMPTY RDI_OBJECT! " << line.remove("\n").toStdString().c_str(); // FIXME: fix this in original generation of these rdi->func() lines
                              }
                          }
                      }
                  }
              }
          }

          if (!declarMode)
            fixedFunc.addCodeLine(line);
      }

    fixedClass.addFunction(fixedFunc);
  }

#if DEBUGMODE
    cout << "DONE" << endl;
    cout << "Fixing " << cls.toStdString().c_str() << "...";
#endif

    QStringList removeTrace;
    foreach (auto trace, tracerx) {
        bool isDigit = true;
        foreach (auto c, trace.first) {
            if (!c.isDigit()) {
                isDigit = false;
                break;
            }
        }
        if (isDigit) {
            //cout << "Found wrong trace: " << trace.first.toStdString().c_str() << endl;
            removeTrace.append(trace.first);
        }
    }
    foreach (QString t, removeTrace) {
        tracerx.erase(t);
    }

    foreach (FixedFunction func, fixedClass.getFunctions()) {
        //foundSomething = false;
        int i = 0;
        QStringList newLines = func.getCodeLines();
        foreach (QString line, func.getCodeLines()) {
            QString linx;
            foreach (auto trace, tracerx) {
                if (line.contains(" " + trace.first + ";")) {
                    linx = line.trimmed().split(';')[0];
                    QStringList declax = linx.split(' ');
                    if (declax.length() <= 2) {
                        //if (!foundSomething) {
                        //    cout << cls.toStdString().c_str() << ": " << func.getName().toStdString().c_str() << " [fixing 2.1]" << endl;
                        //    foundSomething = true;
                        //}
                        line = line.replace(linx + ";", trace.second + "* " + trace.first + ";"); // make pointer for class for now!
                        if (declax[0].contains("STRUCT"))
                          line = line.remove(QRegExp("([\n]+)$")); // was STRUCT before --> " + declax[0] + "\n"

                        newLines[i] = line;

                        //cout << cls.toStdString().c_str() << ": [fixing 2.1] " << trace.first.toStdString().c_str() << " " << line.toStdString().c_str() << endl;
                    }
                } else if (line.contains(trace.first + " = ")) {
                    linx = line.trimmed();
                    linx = linx.split(" = ")[0];
                    QStringList jo = linx.split(' ');
                    if (jo.length() <= 2) {
                        //if (!foundSomething) {
                        //    cout << cls.toStdString().c_str() << ": " << func.getName().toStdString().c_str() << " [fixing 2.2]" << endl;
                        //    foundSomething = true;
                        //}
                        if (jo[0].contains("STRUCT") || ClassStorer::AllValidTypes.contains(jo[0])) {
                            line = line.replace(linx + " = ", trace.second + "* " + trace.first + " = "); // make pointer for class for now!
                            newLines[i] = line;
                            //cout << cls.toStdString().c_str() << ": [fixing 2.2] " << trace.first.toStdString().c_str() << " " << line.toStdString().c_str() << endl;
                        }
                    }
                }
            }
            i++;
        }

        func.setCodeLines(newLines);
        fixedClass.updateFunc(func);
    }

#if DEBUGMODE
  cout << "DONE" << endl;
#endif

  return fixedClass;
}
