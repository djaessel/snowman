#ifndef CLASSSTORER_H
#define CLASSSTORER_H

#include <QDir>
#include <QString>
#include <QTextStream>
#include <QStringList>

#include <bits/stdc++.h>
#include <iostream>

#include "specialvals.h"

#include "rawclass.h"
#include "structer.h"
#include "fixedclass.h"

#include <thread>
#include <QRunnable>
#include <QDebug>
#include <QThread>
#include <QThreadPool>

using namespace std;


class ClassStorer
{
private:
  Structer structer;
  vector<RawClass> classList;

  map<QString, QString> allFuncs;
  map<QString, QString> allFuncClass;

  QString replaceSymbolsInLine(QString line);
  QString classFunctionParameterFix(QString fname, QString assemblyFuncName);

public:
  inline static QString ExportDir;
  inline static map<QString, QString> ParamTypes; // currently unused
  inline static QStringList ParamAsmNames;
  inline static map<QString, QString> Replaces;
  inline static QStringList AllValidTypes;
  inline static QStringList AllValidSpecialTypes;

  static void initValues();

  void writeClasses();
  void writeClassHeaderFile(RawClass cls);
  void writeClassCodeFile(RawClass cls);
  void writeStructsForHeader(RawClass cls);
  void updateNewCppFile(QString filePath/*, vector<RawClass> classes*/);
  void writeClassesJust(map<QString, FixedClass> fixedClasses, map<QString, QStringList> classIncludes);

  ClassStorer(Structer structer, vector<RawClass> classList);
};

class ClassStorerTask : public QRunnable
{
private:
  uint offset, length;
  ClassStorer* classStorer;
  vector<RawClass> *classes;
public:
  ClassStorerTask(ClassStorer* classStorer, vector<RawClass> *classes, uint offset, uint length)
  {
    this->classStorer = classStorer;
    this->classes = classes;
    this->offset = offset;
    this->length = length;
  }

  void run() override
  {
      for (uint i = offset; i < length; i++) {
          classStorer->writeClassHeaderFile(this->classes->at(i));
          classStorer->writeClassCodeFile(this->classes->at(i));
          classStorer->writeStructsForHeader(this->classes->at(i));
      }
  }
};

#endif // CLASSSTORER_H
