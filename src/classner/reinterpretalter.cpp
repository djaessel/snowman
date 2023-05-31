#include "reinterpretalter.h"
#include "classstorer.h"


void ReinterpretAlter::removeReinterpret(vector<RawClass> classList)
{
  cout << "Removing interpret statements..." << endl;

  foreach (RawClass cls, classList) {
      QStringList lines;

#if DEBUGMODE
      cout << cls.getName().toStdString().c_str() << " removing interprets...";
#endif

      QFile file(ClassStorer::ExportDir + QString("/") + cls.getName() + QString(".cpp"));
      if(!file.open(QIODevice::ReadOnly)) {
          cout << "REINTERPRETALTER 1 ERROR: File could not be opened - " << cls.getName().toStdString().c_str() << ".cpp" << endl;
      }

      QTextStream in(&file);
      while(!in.atEnd()) {
          QString line = in.readLine().remove(QRegExp("([\n]{1})$"));
          int indy = line.indexOf("reinterpret_cast<");
          while (indy >= 0) {
              int tempx = line.right(line.length() - indy).split('(')[0].length(); // clammer plus exclusive end
              line = line.left(indy) + line.right(line.length() - indy - tempx); // remove all in between
              indy = line.indexOf("reinterpret_cast<");
          }
          lines.append(line);
      }
      file.close();


      QFile file2(ClassStorer::ExportDir + QString("/") + cls.getName() + QString(".cpp"));
      if(!file2.open(QIODevice::WriteOnly)) {
          cout << "REINTERPRETALTER 2 ERROR: File could not be opened - " << cls.getName().toStdString().c_str() << ".cpp" << endl;
      }

      QTextStream out(&file2);
      foreach (QString line, lines) {
          out << line.toStdString().c_str() << Qt::endl;
      }
      file2.close();

#if DEBUGMODE
      cout << "DONE" << endl;
#endif
  }
}
