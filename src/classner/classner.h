#ifndef CLASSNER_H
#define CLASSNER_H

#include <iostream>

#include <QString>
#include <QStringList>
#include <QTextStream>
#include <QFile>
#include <QRegExp>
#include <QDir>

#include "specialvals.h"

#include "rawclass.h"
#include "rawfunction.h"
#include "classstorer.h"

using namespace std;

class Classner
{
private:
  vector<RawClass> classes;
  void sortFuncsIntoClasses(vector<RawFunction> funcs);
  void saveNewCppFile(QString filePath, QStringList linesToStore);
public:
  Classner();
  vector<RawClass> getClasses() {return classes;}
  int indexOfClass(QString className);
  bool classExists(QString className);
  void readClassFunctions(QString filePath, bool skipNewCpp=false);
};

#endif // CLASSNER_H
