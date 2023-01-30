#ifndef FUNCTIONANALYZER_H
#define FUNCTIONANALYZER_H

#include <bits/stdc++.h>

#include "specialvals.h"

#include "rawclass.h"
#include "fixedclass.h"

#include <thread>
#include <QRunnable>
#include <QDebug>
#include <QThread>
#include <QThreadPool>

class FunctionAnalyzer
{
public:
  FunctionAnalyzer(){}
  map<QString, FixedClass> findOriginalClass(map<QString, FixedClass> *classes);
  FixedClass findOriginalClass(QString cls, map<QString, FixedClass> *classes);
  map<QString, QStringList> addUsedClassImports(map<QString, FixedClass> *classes, vector<RawClass> *rawClasses);
  QStringList addUsedClassImports(QString cls, map<QString, FixedClass> *classes, vector<RawClass> *rawClasses);
  void addUsedCLassImportsHelper(QStringList *includes, map<QString, FixedClass> *classes, QString line, bool sec = false);
};

class FunctionAnalyzerTask : public QRunnable
{
private:
  uint mode;
  uint offset, length;
  FunctionAnalyzer* funcAnalyzer;
  vector<RawClass> *rawClasses;
  map<QString, FixedClass> *classes;
  map<QString, FixedClass> *fixedClasses;
  map<QString, QStringList> *includes;

public:
  FunctionAnalyzerTask(
      FunctionAnalyzer* funcAnalyzer,
      map<QString, QStringList>* includes,
      map<QString, FixedClass> *classes,
      vector<RawClass> *rawClasses,
      uint offset, uint length,
      uint mode = 0) {
    this->funcAnalyzer = funcAnalyzer;
    this->includes = includes;
    this->classes = classes;
    this->rawClasses = rawClasses;
    this->offset = offset;
    this->length = length;
    this->mode = mode;
  }
  FunctionAnalyzerTask(
      FunctionAnalyzer* funcAnalyzer,
      map<QString, FixedClass>* fixedClasses,
      map<QString, FixedClass> *classes,
      uint offset, uint length,
      uint mode = 1) {
    this->funcAnalyzer = funcAnalyzer;
    this->fixedClasses = fixedClasses;
    this->classes = classes;
    this->offset = offset;
    this->length = length;
    this->mode = mode;
  }

  void run() override
  {
      auto it = classes->begin();
      std::advance(it, offset);
      switch (mode){
          case 0:
            for (uint i = offset; i < length; i++) {

#if DEBUGMODE
  #if SPECIAL_DEBUG
        cout << "Add Used Class Imports " << it->first.toStdString().c_str();
  #else
        cout << "Add Used Class Imports " << it->first.toStdString().c_str() << endl;
  #endif
#endif
              includes->insert_or_assign(it->first, funcAnalyzer->addUsedClassImports(it->first, classes, rawClasses));
              if (i < classes->size() - 1)
                  std::advance(it, 1);
#if DEBUGMODE
  #if SPECIAL_DEBUG
        cout << "DONE" << endl;
  #endif
#endif
            }
            break;
          case 1:
            for (uint i = offset; i < length; i++) {
              fixedClasses->insert_or_assign(it->first, funcAnalyzer->findOriginalClass(it->first, classes));
              if (i < classes->size() - 1)
                  std::advance(it, 1);
            }
            break;
          default:
            qDebug() << "ERROR: Wrong mode!!!" << Qt::endl;
            break;
      }
  }
};

#endif // FUNCTIONANALYZER_H
