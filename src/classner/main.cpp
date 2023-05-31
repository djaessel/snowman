#include <iostream>

#include <QCoreApplication>
#include <QElapsedTimer>
#include <QString>

#include "classner.h"
#include "rawclass.h"
#include "structer.h"
#include "classstorer.h"
#include "classreader.h"
#include "reinterpretalter.h"
#include "functionanalyzer.h"

using namespace std;


static bool skipClassWrite = false;
static bool skipReinterpret = false;
static bool skipAnalyze = false;
static bool skipRemoveIncluded = false;
static bool skipClassAnalyze = false;


static bool argumentExists(char* arg, const char* search)
{
  return QString::fromLocal8Bit((const char*)arg, strlen(arg)) == QString(search);
}

static void printElapsedTime(QElapsedTimer *elapsedTimer)
{
  ulong msecs = elapsedTimer->elapsed();
  ulong secs = msecs / 1000;
  if ((msecs % 1000) > 0) secs++;
  ulong hours = secs / 3600;
  secs = secs % 3600;
  ulong mins = secs / 60;
  secs = secs % 60;
  cout << "Time taken: " << hours << ":" << mins << ":" << secs << endl;
}

static void printSkipOptions()
{
  // print options
  cout << "SkipClassWrite: " << ((skipClassWrite) ? "True" : "False") << endl;
  cout << "SkipReinterpret: " << ((skipReinterpret) ? "True" : "False") << endl;
  cout << "SkipAnalyze: " << ((skipAnalyze) ? "True" : "False") << endl;
  cout << "SkipRemoveIncluded: " << ((skipRemoveIncluded) ? "True" : "False") << endl;
  cout << "SkipClassAnalyze: " << ((skipClassAnalyze) ? "True" : "False") << endl;
}


int main(int argc, char *argv[])
{
//  QCoreApplication a(argc, argv);

  QString filePath = "";

  if (argc > 0) {
      filePath = argv[1];
      if (argc > 1) {
          for (int i = 1; i < argc; i++) {
              if (argumentExists(argv[i], "-sc"))
                  skipClassWrite = true;
              else if (argumentExists(argv[i], "-sr"))
                  skipReinterpret = true;
              else if (argumentExists(argv[i], "-sa"))
                  skipAnalyze = true;
              else if (argumentExists(argv[i], "-si"))
                  skipRemoveIncluded = true;
              else if (argumentExists(argv[i], "-sa2"))
                  skipClassAnalyze = true;
              else if (argumentExists(argv[i], "--skip-all")){
                  skipClassWrite = true;
                  skipReinterpret = true;
                  skipAnalyze = true;
                  skipRemoveIncluded = true;
                  skipClassAnalyze = true;
              }
          }
      }
  }

  printSkipOptions();


  if (filePath.isEmpty()) {
      cout << "No file given!" << endl;
      return 1;
  }


  // Start program time watch
  QElapsedTimer elapsedTimer;
  elapsedTimer.start();


  cout << "Processing cpp file ..." << endl;

  ClassStorer::initValues();

  Structer structer;
  structer.readStructs(filePath);

  Classner classner;
  classner.readClassFunctions(filePath, skipClassWrite);
  vector<RawClass> classes = classner.getClasses();

  ClassStorer classStorer(structer, classes);

  if (!skipClassWrite) {
    classStorer.writeClasses();
    classStorer.updateNewCppFile(filePath/*, classes*/);
  }

  if (!skipReinterpret) {
    ReinterpretAlter reinterpret;
    reinterpret.removeReinterpret(classes);
  }

  ClassReader classReader;
  classReader.readClasses();
  map<QString, FixedClass> modifiedClasses = classReader.getClasses();

  // remove default cpp file from class check - change later with different behavior
  QStringList pathArray = filePath.split("/");
  QString fileName = pathArray.back().split(".")[0];
  modifiedClasses.erase(fileName);

  //map<QString, FixedClass> bakModClasses;
  //foreach (auto c, modifiedClasses) {
  //    bakModClasses.insert_or_assign(c.first, c.second);
  //}

  if (!skipAnalyze) {
      FunctionAnalyzer funcAnalyzer;
      map<QString, FixedClass> fixedClasses = funcAnalyzer.findOriginalClass(&modifiedClasses);
      map<QString, QStringList> classIncludes = funcAnalyzer.addUsedClassImports(&fixedClasses, &classes); // FIXME: bottleneck!!!
      // fixed_classes = analyzer.removeInvalidParams(fixed_classes, classes) # FIXME: broken at the moment
      classStorer.writeClassesJust(fixedClasses, classIncludes);
  }

  if (!skipRemoveIncluded) {
      cout << "Remove included [not implemented yet]" << endl;
      // TODO: Python equivalen: os.system("cd generated_classes && python3 remove_included.py")
  }

  if (!skipClassAnalyze) {
      cout << "Class Analyze [not implemented yet]" << endl;
      // TODO: Python equivalent
      // classAnalyzer = ClassAnalyzer()
      // classAnalyzer.findClassAttributes(bak_mod_classes) # FIXME: only works when previous are done and skipped second run
      // - - -
      //gotogo = Gotogo()
      //gotogo.processClasses(modified_classes)
      //os.system("mv *_*.cpp endl/class_info/") # FIXME: change later
  }


  // Stop program time watch
  printElapsedTime(&elapsedTimer);
  elapsedTimer.invalidate();

  return 0;
}
