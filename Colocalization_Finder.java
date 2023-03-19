/*
 * Colocalization_Finder.java
 *
 * Created on 20/01/2005 Copyright (C) 2005 IBMP
 * ImageJ plugin
 * 
 * Version  : 1.1
 * Authors  : C. Laummonerie & J. Mutterer
 *            written for the IBMP-CNRS Strasbourg(France)
 * Email    : jerome.mutterer at ibmp-ulp.u-strasbg.fr
 * Description :  This plugin displays a correlation diagram for two 
 * images (8bits, same size). Drawing a rectangular selection 
 * on this diagram allows you to highlight corresponding pixels on a
 * RGB overlap of the original images, and if selected, on a 3rd image.
 * Analysis can be restricted to pixels having values with a minimum ratio.
 * Selection settings are logged to a results window. Large parts of this 
 * code were taken from Wayne Rasband, Pierre Bourdoncle.
 * and Gary Chinga.
 * 
 * Version 1.2 : JM
 * - Rewrote the mask overlay part, now faster
 * - Made the scatterplot selection possible with any kind of closed selections after several requests.
 * - The ratio bars are now overlaid on a separte layer, so that you stillcan read the pixel info behind these bars
 * - Fixed the Fire LUT issue (LUT was not always applied) 
 *  
 * Version 1.3 : Philippe Carl
 * Email       : philippe.carl at unistra.fr
 * Date        : 4/30/2016
 * - Replacement of the deprecated functions (getBoundingRect, IJ.write) by the new ones
 * - Extension of the plugin for whatever picture dynamics
 * - Addition of a plot (with legends, ticks (minor and major), labels) within the scatter plot
 * - The selected points within the overlay picture are updated as soon as the ROI in the scatter plot is modified or dragged over
 * - Possibility to move the ROI position (within the scatter plot) from the mouse position within the overlay picture
 * - Possibility to set ROIs with given colors with a mouse double click
 * - Possibility to generate the x or y histogram with a Gaussian fit in order to extract the histogram maximum position by using the numeric pad 4/6 or 2/8 keys
 *  
 * Version 1.4 : Philippe Carl
 * Date        : 10/20/2019
 * - Addition of scripting possibilities through plugin or macro programming
 * - The colocalization calculations are performed using double parameters instead of float
 * - Possibility to reduce the analysis to a ROI within the composite picture
 * 
 * Version 1.5: Philippe Carl
 * Date       : 12/15/2019
 * - Possibility to add a selection within the Composite picture to restric the analysis a the given selection
 * - Addition of synchronized background thread for smoothly updating the calculations on the fly
 * 
 * Version 1.6: Philippe Carl
 * Date       : 06/12/2022
 * - Possibility to choose the size of the scatter plot upon start of the plugin
 * - Addition of a label panel at the bottom of the scatterPlot picture displaying the limits of the scatterPlot Roi selection (or other parameters upon selection)
 * - Addition of a "Set" button at the bottom left of the scatterPlot picture allowing so set the limits of the scatterPlot graph and/or of the scatterPlot Roi  and/or choosing the displayed parameters within the label panel at the bottom of the scatterPlot (the 'g' key gives the same features)
 * - Addition of the Manders coefficients (M1, M2 and M1_norm, M2_norm) calculation 
 * - The possibility to set ROIs with given colors with a mouse double click has been erased (due to the ImageJ 1.53c 26 June 2020 update) and replaced by a Ctrl + mouse click user action
 * 
 * Version 1.7: Philippe Carl
 * Date       : 18/03/2023
 * - Addition of a ScatterPlot_ROI_name column within the Colocalization Finder Results window
 * 
 *   This program is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; either version 2 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program; if not, write to the Free Software
 *   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 */
import ij.IJ;
import ij.Prefs;
import ij.ImageListener;
import ij.ImagePlus;
import ij.WindowManager;

import ij.gui.GenericDialog;
import ij.gui.ImageCanvas;
import ij.gui.ImageWindow;
import ij.gui.Overlay;
import ij.gui.Roi;
import ij.gui.RoiListener;
import ij.gui.ShapeRoi;
import ij.gui.Toolbar;

import ij.measure.CurveFitter;

import ij.plugin.Colors;
import ij.plugin.PlugIn;
import ij.plugin.RGBStackMerge;
import ij.plugin.filter.ThresholdToSelection;
import ij.plugin.frame.Fitter;
import ij.plugin.frame.RoiManager;

import ij.process.ByteProcessor;
import ij.process.ImageConverter;
import ij.process.ImageProcessor;
import ij.process.ImageStatistics;
import ij.process.ShortProcessor;

import ij.text.TextWindow;

import ij.util.ArrayUtil;
import ij.util.Tools;

import java.awt.Button;
import java.awt.Checkbox;
import java.awt.Choice;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Image;
import java.awt.Label;
import java.awt.Rectangle;
import java.awt.Toolkit;
import java.awt.datatransfer.Clipboard;
import java.awt.datatransfer.StringSelection;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.WindowEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.Panel;
import java.awt.Point;

import java.net.URL;

import java.util.Arrays;

import javax.swing.Timer;

public class Colocalization_Finder implements	PlugIn, ActionListener, ItemListener, ImageListener, RoiListener, KeyListener, MouseListener, MouseMotionListener, Runnable
{
	private static int 							multiClickInterval;
	private Thread								bgThread;		// thread for launching the calculation (in the background)
			Toolkit								toolkit;
			Integer								interval;
			Timer								timer;
			ImageCanvas							canvas, canvasResu, ccr, cc3, icc;
			ImageConverter						image1Converter , image2Converter;
			ImagePlus							image1          , image2         ,                         imp                  , insertImp, insertImp2, insertImp3;
			ImageStatistics						image1Statistics, image2Statistics;
			boolean								previousblackBackgroundState;
			boolean								mouseInsideResultImage	= false;
			boolean								mouseInsideScatterPlot	= false;
			boolean								scatterPlotModified		= false;
			boolean								resultImageModified		= false;
			String							[]	selectedItemsLabels = {"Pearson's_Rr"	, "Overlap_R"	, "k1"		, "k2"		, "M1"		, "M2"		, "M1_norm"		, "M2_norm"		, "Slope"	, "Intercept"	, "nb_pixels"	, "%pixels"				, "min_I1"		, "max_I1"		, "min_I2"		, "max_I2"		};
//			boolean							[]	selectedItemsValues = {show_Pearson_s_Rr, show_Overlap_R, show_k1	, show_k2	, show_M1	, show_M2	, show_M1_norm	, show_M2_norm	, show_Slope, show_Intercept, show_nb_pixels, show_percentage_pixels, show_min_I1	, show_max_I1	, show_min_I2	, show_max_I2	};
			int								[]	wList;
			String								str;
			int									scatterPlotSizeIndex;
			String							[]	scatterPlotSizeText		= {"_256 x 256_", "_512 x 512_", "1024 x 1024"};
//			String							[]	scatterPlotSizeText		= {"_256 \u00D7 256_", "_512 \u00D7 512_", "1024 \u00D7 1024"};
			Button								set;
			Checkbox						[]	checkboxes;
			Component						[]	dlgItems;
			Image								insert					= null;
	static	Image								icon					= null;
	static	Colocalization_Finder				instance;
	static	GenericDialog						gd;
	static	ImagePlus															   scatterPlot             , resultImage;
	static	ImageProcessor						image1Processor , image2Processor, scatterPlotProcessor;
	static	ImageProcessor						mask, colocMask;
	static	ImageWindow			   				                                   scatterPlotWindow;
	static	ThresholdToSelection				ts;
	static	Overlay								                                   scatterplotOverlay       , resultImageOverlay;
	static	CurveFitter							cf;
	static	TextWindow							ResultsWindow;
	static	String																							  resultImageRoiName;
	static	     Roi							colocMaskRoi,                      scatterPlotRoi           , resultImageRoi;
	static	ShapeRoi							sr1, sr2;
	static	RoiManager							rm;
	static	Rectangle							coord, rect;
	static	Label								statusLabel;
	static	String								title        = "Colocalization Finder";
	static	String								ResultsTitle = "Colocalization Finder Results";
	static	String								ResultsHeadings, spaceString;
	static	boolean								pearson					= true;
	static	boolean								comparisonRunning		= false;
//	static	boolean								doubleClick;
	static	final int							show_Pearson			= 0x1;
	static	final int							show_Overlap			= 0x2;
	static	final int							show_k1					= 0x4;
	static	final int							show_k2					= 0x8;
	static	final int							show_M1					= 0x10;
	static	final int							show_M2					= 0x20;
	static	final int							show_M1_norm			= 0x40;
	static	final int							show_M2_norm			= 0x80;
	static	final int							show_Slope				= 0x100;
	static	final int							show_Intercept			= 0x200;
	static	final int							show_nb_pixels			= 0x400;
	static	final int							show_percentage_pixels	= 0x800;
	static	final int							show_min_I1				= 0x1000;
	static	final int							show_max_I1				= 0x2000;
	static	final int							show_min_I2				= 0x4000;
	static	final int							show_max_I2				= 0x8000;
	static	final int							default_checked			= show_Pearson + show_min_I1 + show_max_I1 + show_min_I2 + show_max_I2;
	static	int									show_checked			= default_checked;
	static	int									nbChecked				= 5;
	static int									precision				= 8;
//	static	int									i, scatterPlotSize, npixels, clickCount, counter, i1Index, i2Index, i3Index, x, y, z1, z2, count;
	static	int									i, scatterPlotSize, npixels, counter, i1Index, i2Index, i3Index, x, y, z1, z2, count;
	static	int									windowOffset, xOffset, yOffset, w1, w2, h1, h2, roiWidth, roiHeight;
	static	int									vi1, vi2, pos, color;
	static	double								val, percentPixels, min1, min2, max1, max2, minI1, maxI1, maxI2, minI2, depth1, depth2;
	static	double								scatterPlotMin1, scatterPlotMax1, scatterPlotMin2, scatterPlotMax2;
	static	double								PearsonValue, xMean, yMean, xStd, yStd;						// Variables from getR(double[] d1, double[] d2) that are made global to be able to be outputed
	static	String								PearsonValueAsString;
	static	byte							[]	maskPixels;
	static	double							[]	intx, inty, lesx, lesy, cfParams;
	static	String							[]	titles;
	static	Point							[]	pointsInsideRoi;
	static	ColorDefinition					[]	colors;



	public Colocalization_Finder()
	{
		toolkit						=			Toolkit.getDefaultToolkit();
		interval					= (Integer) toolkit.getDesktopProperty("awt.multiClickInterval");
		if (interval == null)
			multiClickInterval		= 200;
		else
			multiClickInterval		= interval.intValue();
	}

	public void run(String arg)
	{
		if (IJ.versionLessThan("1.52r"))
			return;
		IJ.register						(Colocalization_Finder.class);
		previousblackBackgroundState	= Prefs.blackBackground;
		Prefs.blackBackground			= false;
		instance						= this;

		try
		{
			URL url		= getClass().getResource("/image/coloc_icon.png");
			icon		= Toolkit.getDefaultToolkit().getImage(url);
		}
		catch (Exception e)
		{
			IJ.showMessage("Loading the icon picture", "The icon picture \"/image/coloc_icon.png\" could not be found!");
		}

		try
		{
			URL url1	= getClass().getResource("/image/coloc_insert.png");
			insert		= Toolkit.getDefaultToolkit().getImage(url1);
		}
		catch (Exception e)
		{
			IJ.showMessage("Loading the insert picture", "The insert picture \"/image/coloc_insert.png\" could not be found!");
		}
		insertImp		= new ImagePlus		("Error message", insert);

		try
		{
			URL url2	= getClass().getResource("/image/area_chart.png");
			insert		= Toolkit.getDefaultToolkit().getImage(url2);
		}
		catch (Exception e)
		{
			IJ.showMessage("Loading the insert picture", "The insert picture \"/image/area_chart.png\" could not be found!");
		}
		insertImp2		= new ImagePlus		("Error message", insert);

		try
		{
			URL url3	= getClass().getResource("/image/select_points.png");
			insert		= Toolkit.getDefaultToolkit().getImage(url3);
		}
		catch (Exception e)
		{
			IJ.showMessage("Loading the insert picture", "The insert picture \"/image/select_points.png\" could not be found!");
		}
		insertImp3		= new ImagePlus		("Error message", insert);

		if (arg.equals("about"))
		{
			showAbout();
			return;
		}

		wList = WindowManager.getIDList();
		if (wList == null || wList.length < 2)
		{
			IJ.showMessage(title, "There must be at least two windows open");
			return;
		}

		titles = new String[wList.length];
		for (i = 0; i < wList.length; i++)
		{
			imp = WindowManager.getImage(wList[i]);
			if (imp != null)
				titles[i] = imp.getTitle();
			else
				titles[i] = "";
		}
		scatterPlotSizeIndex = WindowManager.getImage(wList[0]).getBitDepth() / 16;

		if (!showDialog())
			return;

		ResultsHeadings = "picture1_name\tpicture2_name\tScatterPlot_ROI_name\tPearson's_Rr\tAverage_a\tAverage_b\tSigma_a\tSigma_b\tOverlap_R\tk1\tk2\tM1\tM2\tM1_norm\tM2_norm\tSlope\tIntercept\tnb_pixels\t%pixels\tmin_I1\tmax_I1\tmin_I2\tmax_I2\t<picture1>\t<picture2>\tROI_color";
		defineColors();

		build_scatter_plot();
		IJ.run(scatterPlot, "Fire", "");
		IJ.run(scatterPlot, "Enhance Contrast", "saturated=0.5");

//		resultImage.show();
		comparison(false, false);
	}

	public void run()
	{
		while (true)
		{
//			IJ.wait(50);								// delay to make sure the roi has been updated
				 if (scatterPlotModified && !comparisonRunning)
			{
				comparison(false, false);
				scatterPlot.draw();
			}
			else if (resultImageModified && !comparisonRunning)
			{
				rebuild_scatter_plot();
				comparison(false, false);
			}
			synchronized (this)
			{
				if (scatterPlotModified)
				{
					scatterPlotModified = false;		// and loop again
				}
				else if (resultImageModified)
				{
					resultImageModified = false;		// and loop again
				}
				else
				{
					try
					{
						wait();							// notify wakes up the thread
					}
					catch(InterruptedException e)
					{
						return;							// interrupted tells the thread to exit
					}
				}
			}
		}
	}

	public boolean showDialog()
	{
		gd						= new GenericDialog(title);
		gd						.addChoice				("Image_1 (will be shown in red):     "             , titles             , titles[0]                                );
		gd						.addChoice				("Image_2 (will be shown in green):"                , titles             , titles[1]                                );
		gd						.addChoice				("ScatterPlot_Size:                                ", scatterPlotSizeText, scatterPlotSizeText[scatterPlotSizeIndex]);
		gd						.setIconImage			(icon);
		Choice theChoice		= (Choice)				(gd.getChoices().lastElement());
		gd						.pack					();
		theChoice				.requestFocusInWindow	();
		gd.showDialog();
		if (gd.wasCanceled())
			return false;
		i1Index					= gd.getNextChoiceIndex	();
		i2Index					= gd.getNextChoiceIndex	();
		scatterPlotSizeIndex	= gd.getNextChoiceIndex	();
		image1					= WindowManager.getImage(wList[i1Index]).duplicate();
		image2					= WindowManager.getImage(wList[i2Index]).duplicate();
		WindowManager			.getImage(wList[i1Index]).getWindow().setIconImage(icon);
		WindowManager			.getImage(wList[i2Index]).getWindow().setIconImage(icon);

		switch(scatterPlotSizeIndex)
		{
			case 0:
				scatterPlotSize	=  256;
			break;
			case 1:
				scatterPlotSize	=  512;
			break;
			case 2:
				scatterPlotSize	= 1024;
			break;
			default:
				scatterPlotSize	=  512;
			break;
		}

		w1						= image1.getWidth();
		w2						= image2.getWidth();
		h1						= image1.getHeight();
		h2						= image2.getHeight();

		if (w1 != w2 || h1 != h2)
		{
			IJ.showMessage(title, "Images 1 and 2 must be at the same height and width");
			return false;
		}

		image1Statistics		= image1.getStatistics();
		image2Statistics		= image2.getStatistics();
		scatterPlotMin1 = min1	= image1Statistics.min;
		scatterPlotMax1 = max1	= image1Statistics.max;
		scatterPlotMin2 = min2	= image2Statistics.min;
		scatterPlotMax2 = max2	= image2Statistics.max;
		depth1					= Math.pow(2, image1.getBitDepth());
		depth2					= Math.pow(2, image2.getBitDepth());

		// create the overlay and mask image.
		ImagePlus[] images		= { image1, image2 };
		resultImage				= RGBStackMerge.mergeChannels		(images, true);
		resultImage				.show								();
		resultImage				.getWindow().setIconImage			(icon);
		resultImage				.getCanvas().addMouseListener		(this);
		resultImage				.getCanvas().addMouseMotionListener	(this);

		maskPixels				= new byte[w1 * h1];
		Arrays					.fill								(maskPixels, (byte) 0);

		if(titles[i1Index].lastIndexOf(".") > 0)
			resultImage			.getImageStack().setSliceLabel		(titles[i1Index].substring(0, titles[i1Index].lastIndexOf("."))	, 1);
		else
			resultImage			.getImageStack().setSliceLabel		(titles[i1Index]													, 1);
		if(titles[i2Index].lastIndexOf(".") > 0)
			resultImage			.getImageStack().setSliceLabel		(titles[i2Index].substring(0, titles[i2Index].lastIndexOf("."))	, 2);
		else
			resultImage			.getImageStack().setSliceLabel		(titles[i2Index]													, 2);

		windowOffset			= 80;
		scatterPlot				= new ImagePlus						("ScatterPlot", new ByteProcessor (scatterPlotSize + windowOffset, scatterPlotSize + windowOffset));
		scatterPlot				.addImageListener					(this);

		scatterPlot				.show								();
		scatterPlotWindow		= scatterPlot.getWindow				();
		scatterPlotWindow		.addKeyListener     	    		(this);
		scatterPlotWindow		.setIconImage						(icon);
		canvas					= scatterPlotWindow.getCanvas		();
		canvas					.addKeyListener						(this);
		canvas					.addMouseListener					(this);

		Panel bottomPanel		= new Panel							();
		int hgap				= IJ.isMacOSX						()?1:5;
		set						= new Button						(" Set ");
		set						.addActionListener					(this);
		set						.addKeyListener						(this);
		bottomPanel				.add								(set);
		bottomPanel				.setLayout							(new FlowLayout(FlowLayout.RIGHT,hgap,0));
		statusLabel				= new Label							();
		statusLabel				.setFont							(new Font("Monospaced", Font.PLAIN, 12));
		statusLabel				.setBackground						(new Color(220, 220, 220));
		bottomPanel				.add								(statusLabel);
		scatterPlotWindow		.add								(bottomPanel);
		statusLabel				.setPreferredSize					(new Dimension(scatterPlotWindow.getWidth() -  73, statusLabel.getPreferredSize().height));
//		spaceString				= String.format						("%1$" +  Math.round(0.047 * scatterPlotWindow.getWidth() - 20) + "s", " ");
		spaceString				= String.format						("%1$" +  Math.round(0.039 * scatterPlotWindow.getWidth() - 21) + "s", " ");
		scatterPlotWindow		.pack();

		return true;
	}

	public void build_scatter_plot()
	{
		xOffset					= 60;
		yOffset					= windowOffset - xOffset;
		image1Processor			= image1.getProcessor();
		image2Processor			= image2.getProcessor();
		scatterPlotProcessor	= scatterPlot.getProcessor();

		for (y = 0; y < h1; y++)
		{
			for (x = 0; x < w1; x++)
			{
				z1				=                   (int) (image1Processor    .getPixelValue(x, y) * scatterPlotSize / scatterPlotMax1);
				z2				= scatterPlotSize - (int) (image2Processor    .getPixelValue(x, y) * scatterPlotSize / scatterPlotMax2);
				count			=                   (int) scatterPlotProcessor.getPixelValue(z1 + xOffset, z2 + yOffset);
				count++;
				scatterPlotProcessor.putPixelValue(z1 + xOffset, z2 + yOffset, count);
			}
		}
//		scatterPlot				.setRoi(new Roi(xOffset + scatterPlotSize + 1 - 150, yOffset, 150, 150));
		scatterPlot				.setRoi(new Roi(xOffset, yOffset, scatterPlotSize + 1, scatterPlotSize + 1));
//		scatterPlot				.setRoi(new Roi(xOffset + 20, yOffset, 237, 237));
		scatterPlotRoi			= scatterPlot.getRoi();
		scatterPlotRoi			.addRoiListener(this);
//		resultImageRoi			= resultImage.getRoi();
//		resultImageRoi			.addRoiListener(this);

		build_plot_for_scatter_plot();
	}

	static public void rebuild_scatter_plot()
	{
		for (y = 0; y <= scatterPlotSize; y++)
			for (x = 0; x <= scatterPlotSize; x++)
				scatterPlotProcessor.putPixelValue(x + xOffset, y + yOffset, 0);

		resultImageRoi			= resultImage.getRoi();
		if (resultImageRoi != null)
		{
			rect				= resultImageRoi.getBounds();
			if (rect.width == 0 || rect.height == 0)
				resultImageRoi = null;
		}

		if(resultImageRoi == null)
		{
			// There is no ROI within the result image, thus I make the analysis within the whole picture
			for (y = 0; y < h1; y++)
			{
				for (x = 0; x < w1; x++)
				{
					if(image1Processor.getPixelValue(x, y) > scatterPlotMin1 && image2Processor.getPixelValue(x, y) > scatterPlotMin2)
					{
						z1				=                   (int) ((    image1Processor.getPixelValue(x, y) - scatterPlotMin1) * scatterPlotSize / (scatterPlotMax1 - scatterPlotMin1));
						z2				= scatterPlotSize - (int) ((    image2Processor.getPixelValue(x, y) - scatterPlotMin2) * scatterPlotSize / (scatterPlotMax2 - scatterPlotMin2));
						count			=                   (int)  scatterPlotProcessor.getPixelValue(z1 + xOffset, z2 + yOffset);
						count++;
						scatterPlotProcessor.putPixelValue(z1 + xOffset, z2 + yOffset, count);
					}
				}
			}
		}
		else
		{	// There a no ROI within the result image, thus I make the analysis only within the ROI elements
			pointsInsideRoi = resultImageRoi.getContainedPoints();

			for (i = 0; i != pointsInsideRoi.length; i++)
			{
				if(pointsInsideRoi[i].x >= 0 && pointsInsideRoi[i].x < w1 && pointsInsideRoi[i].y >= 0 && pointsInsideRoi[i].y < h1)
				{
					if(image1Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) > scatterPlotMin1 && image2Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) > scatterPlotMin2)
					{
						z1				=                   (int) (((   image1Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y)) - scatterPlotMin1) * scatterPlotSize / (scatterPlotMax1 - scatterPlotMin1));
						z2				= scatterPlotSize - (int) (((   image2Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y)) - scatterPlotMin2) * scatterPlotSize / (scatterPlotMax2 - scatterPlotMin2));
						count			=                   (int)  scatterPlotProcessor.getPixelValue(z1 + xOffset, z2 + yOffset);
						count++;
						scatterPlotProcessor.putPixelValue(z1 + xOffset, z2 + yOffset, count);
					}
				}
			}
		}
		scatterPlot.updateAndDraw();
	}

	public static String analyze(boolean _write_results, boolean _set_roi, String separator)
	{
		rebuild_scatter_plot();
		return comparison(_write_results, _set_roi);
	}

	public static String analyze(boolean _write_results, boolean _set_roi)
	{
		return analyze(_write_results, _set_roi, ";");
	}
	
	public static String analyze(boolean _write_results, boolean _set_roi, int[] _outputIDs, String separator)
	{
		int 		i;
		String 		output;
		String	[]	outputs;

		rebuild_scatter_plot();
		output = comparison(_write_results, _set_roi);

		Arrays.sort(_outputIDs);
		outputs	= Tools.split(output, ";");
		output	= _outputIDs[0] < outputs.length ? outputs[_outputIDs[0]] : "outOfBoundsOfChosenIndex";
		for(i = 1; i != _outputIDs.length; i++)
			if(_outputIDs[i] < outputs.length)
				output += separator + outputs[_outputIDs[i]];
			else
				output += separator + "outOfBoundsOfChosenIndex";

		return output;
	}

	public static String analyze(boolean _write_results, boolean _set_roi, int[] _outputIDs)
	{
		return analyze			(_write_results, _set_roi, _outputIDs, ";");
	}
	
	// call("Colocalization_Finder.analyzeByMacro", _write_results);
	public static String analyzeByMacro(String _write_results)
	{
		return analyze			(Boolean.valueOf(_write_results), false);
	}

	// call("Colocalization_Finder.analyzeByMacro", _write_results, _set_roi);
	public static String analyzeByMacro(String _write_results, String _set_roi)
	{
		return analyze			(Boolean.valueOf(_write_results), Boolean.valueOf(_set_roi));
	}

	public static String analyzeByMacro(String _write_results, String _set_roi, String _outputIDs)
	{
		return analyzeByMacro	(_write_results, _set_roi, _outputIDs, ";");
	}

	// call("Colocalization_Finder.getResultsLinesCount");
	public static String getResultsLinesCount()
	{
		ResultsWindow = (TextWindow) WindowManager.getWindow(ResultsTitle);
		if(ResultsWindow == null)
			return String.valueOf(0);
		return String.valueOf(ResultsWindow.getTextPanel().getLineCount());
	}

	public static String analyzeByMacro(String _write_results, String _set_roi, String _outputIDs, String separator)
	{
		int			i, j;
		int		[]	outputIDs		, outputIDsSub;
		String	[]	outputIDSplitted, outputIDSplittedSub, outputIDSplittedFull;

		outputIDSplitted	= Tools.split(_outputIDs, ",");
		for(i = 0; i != outputIDSplitted.length; i++)
		{
			if(outputIDSplitted[i].indexOf("-") != -1)
			{
				outputIDSplittedSub		= Tools.split(outputIDSplitted[i], "-");
				outputIDsSub			= new int[2];
				outputIDsSub[0]			= Integer.valueOf(outputIDSplittedSub[0]);
				outputIDsSub[1]			= Integer.valueOf(outputIDSplittedSub[1]);
				Arrays.sort				(outputIDsSub);
				for(j = i; j != outputIDSplitted.length - 1; j++)
					outputIDSplitted[j] = outputIDSplitted[j + 1];
				outputIDSplitted[outputIDSplitted.length - 1] = String.valueOf(outputIDsSub[0]);
				outputIDSplittedSub		= new String[outputIDsSub[1] - outputIDsSub[0]];
				for(j = 0; j != outputIDSplittedSub.length; j++)
					outputIDSplittedSub[j] = String.valueOf(outputIDsSub[0] + 1 + j);
				outputIDSplittedFull	= Arrays.copyOf(outputIDSplitted, outputIDSplitted.length + outputIDSplittedSub.length);
				System.arraycopy		(outputIDSplittedSub, 0, outputIDSplittedFull, outputIDSplitted.length, outputIDSplittedSub.length);
				outputIDSplitted		= outputIDSplittedFull;
				i--;
			}
		}
		outputIDs			= new int[outputIDSplitted.length];
		for(i = 0; i != outputIDSplitted.length; i++)
			outputIDs[i] = Integer.valueOf(outputIDSplitted[i]);

		return analyze(Boolean.valueOf(_write_results), Boolean.valueOf(_set_roi), outputIDs, separator);
	}

	// call("Colocalization_Finder.setScatterPlotRoi", 0, 500, 100, 200);
	public static void setScatterPlotRoi(String _minI1, String _maxI1, String _minI2, String _maxI2)
	{
		try								{	minI1			= Double.valueOf(_minI1)			;}
		catch(NumberFormatException e)	{	minI1			= scatterPlotMin1					;}

		try								{	maxI1			= Double.valueOf(_maxI1)			;}
		catch(NumberFormatException e)	{	maxI1			= scatterPlotMax1					;}

		try								{	minI2			= Double.valueOf(_minI2)			;}
		catch(NumberFormatException e)	{	minI2			= scatterPlotMin2					;}

		try								{	maxI2			= Double.valueOf(_maxI2)			;}
		catch(NumberFormatException e)	{	maxI2			= scatterPlotMax2					;}

		setScatterPlotRoi(minI1, maxI1, minI2, maxI2);
	}

	// call("Colocalization_Finder.setScatterPlotLimits", 0, 500, 100, 200);
	public static void setScatterPlotLimits(String _scatterPlotMin1, String _scatterPlotMax1, String _scatterPlotMin2, String _scatterPlotMax2)
	{
		try								{	scatterPlotMin1	= Double.valueOf(_scatterPlotMin1)	;}
		catch(NumberFormatException e)	{	scatterPlotMin1	= min1								;}

		try								{	scatterPlotMax1	= Double.valueOf(_scatterPlotMax1)	;}
		catch(NumberFormatException e)	{	scatterPlotMax1	= max1								;}

		try								{	scatterPlotMin2	= Double.valueOf(_scatterPlotMin2)	;}
		catch(NumberFormatException e)	{	scatterPlotMin2	= min2							;}

		try								{	scatterPlotMax2	= Double.valueOf(_scatterPlotMax2)	;}
		catch(NumberFormatException e)	{	scatterPlotMax2	= max2								;}

		scatterPlotProcessor		.setColor(Color.black);
		scatterPlotProcessor		.resetRoi();
		scatterPlotProcessor		.fill();
		setScatterPlotGraphLimits	();
		build_plot_for_scatter_plot	();
		rebuild_scatter_plot		();
		setScatterPlotRoi			(minI1, maxI1, minI2, maxI2);
	}

	private static void setScatterPlotGraphLimits()
	{
		scatterPlotMin1			= Double.isNaN(scatterPlotMin1)	|| scatterPlotMin1 < 0		? 0					: scatterPlotMin1;
		scatterPlotMax1			= Double.isNaN(scatterPlotMax1)	|| scatterPlotMax1 > depth1	? depth1			: scatterPlotMax1;
		scatterPlotMin2			= Double.isNaN(scatterPlotMin2)	|| scatterPlotMin2 < 0		? 0					: scatterPlotMin2;
		scatterPlotMax2			= Double.isNaN(scatterPlotMax2)	|| scatterPlotMax2 > depth2	? depth2			: scatterPlotMax2;
	}

	private static void setScatterPlotRoi(double minI1, double maxI1, double minI2, double maxI2)
	{
		double xtemp, ytemp, wtemp, htemp;

		minI1					= Double.isNaN(minI1)			|| minI1 < scatterPlotMin1	? scatterPlotMin1	: minI1;
		maxI1					= Double.isNaN(maxI1)			|| maxI1 > scatterPlotMax1	? scatterPlotMax1	: maxI1;
		minI2					= Double.isNaN(minI2)			|| minI2 < scatterPlotMin2	? scatterPlotMin2	: minI2;
		maxI2					= Double.isNaN(maxI2)			|| maxI2 > scatterPlotMax2	? scatterPlotMax2	: maxI2;

		xtemp					= scatterPlotSize / (scatterPlotMax1 - scatterPlotMin1) * (minI1 - scatterPlotMin1) + xOffset;
		wtemp					= scatterPlotSize / (scatterPlotMax1 - scatterPlotMin1) * (maxI1 - scatterPlotMin1) + xOffset                   + 1 - xtemp;
		ytemp					= scatterPlotSize / (scatterPlotMin2 - scatterPlotMax2) * (maxI2 - scatterPlotMin2) + yOffset + scatterPlotSize;
		htemp					= scatterPlotSize / (scatterPlotMin2 - scatterPlotMax2) * (minI2 - scatterPlotMin2) + yOffset + scatterPlotSize + 1 - ytemp;

		scatterPlotRoi			=  new Roi(xtemp, ytemp, wtemp, htemp);
		scatterPlot				.setRoi(scatterPlotRoi);
	}

	private static boolean setScatterPlotRoiLimits()
	{
		boolean changed			= false;

		scatterPlotRoi			=		scatterPlot		.getRoi();
		if(scatterPlotRoi == null)
		{
			scatterPlotRoi =  new Roi(xOffset, yOffset, scatterPlotSize + 1, scatterPlotSize + 1);
//			scatterPlotRoi =  new Roi(xOffset + 20, yOffset, 237, 237);
			scatterPlot.setRoi(scatterPlotRoi);
		}
		else
		{
			rect				=		scatterPlotRoi	.getBounds();
			if (rect.width == 0 || rect.height == 0)
			{
				scatterPlotRoi =  new Roi(xOffset, yOffset, scatterPlotSize + 1, scatterPlotSize + 1);
//				scatterPlotRoi =  new Roi(xOffset + 20, yOffset, 237, 237);
				scatterPlot.setRoi(scatterPlotRoi);
			}
		}

		coord					=         scatterPlotRoi.getBounds();
		minI1					= (int) ( scatterPlotMin1 + (                  coord.x - xOffset                   ) * (scatterPlotMax1 - scatterPlotMin1) / scatterPlotSize );
		maxI1					= (int) ( scatterPlotMin1 + (                  coord.x - xOffset + coord.width  - 1) * (scatterPlotMax1 - scatterPlotMin1) / scatterPlotSize );
		minI2					= (int) ( scatterPlotMin2 + (scatterPlotSize - coord.y + yOffset - coord.height + 1) * (scatterPlotMax2 - scatterPlotMin2) / scatterPlotSize );
		maxI2					= (int) ( scatterPlotMin2 + (scatterPlotSize - coord.y + yOffset                   ) * (scatterPlotMax2 - scatterPlotMin2) / scatterPlotSize );
/*
		minI1					=                                   coord.x - xOffset;
		maxI1					=                                   coord.x - xOffset + coord.width  - 1;
		minI2					=                 scatterPlotSize - coord.y + yOffset - coord.height + 1;
		maxI2					=                 scatterPlotSize - coord.y + yOffset;
*/
		if(!IJ.shiftKeyDown())
		{
			if(minI1 < scatterPlotMin1 || minI1 > scatterPlotMax1)
			{
				minI1	= scatterPlotMin1;
				changed	= true;
			}
			if(maxI1 < scatterPlotMin1 || maxI1 > scatterPlotMax1)
			{
				maxI1	= scatterPlotMax1;
				changed	= true;
			}
			if(minI2 < scatterPlotMin2 || minI2 > scatterPlotMax2)
			{
				minI2	= scatterPlotMin2;
				changed	= true;
			}
			if(maxI2 < scatterPlotMin2 || maxI2 > scatterPlotMax2)
			{
				maxI2	= scatterPlotMax2;
				changed	= true;
			}
		}

		return changed;
	}

	static String comparison(boolean write_results, boolean set_roi)
	{
		if(!comparisonRunning)
			comparisonRunning = true;
		else
		{
			comparisonRunning = false;
//			IJ.log("comparison already running!");
			return "comparison already running!";
		}

		if (Toolbar.getInstance().getToolId() > 4)
		{
			gd						= new GenericDialog("Setting analysis ROI");
			gd.setIconImage			(icon);
			gd.addMessage			("A Selection Tool needs to be chosen in order to modify the analysis ROI.\r\n\r\n              Do you want the Rectangular_Selection_Tool to be set?");
			gd.setOKLabel			("Yes");
			gd.setCancelLabel		("No");
			gd.showDialog();

			if (gd.wasCanceled())
				return "";

			Toolbar.getInstance().setTool(Toolbar.RECTANGLE);
		}

		counter			= 0;

		if(setScatterPlotRoiLimits())
			setScatterPlotRoi(minI1, maxI1, minI2, maxI2);

		resultImageRoi	= resultImage.getRoi();
		if(resultImageRoi != null)
		{
			rect				= resultImageRoi.getBounds();
			if (rect.width == 0 || rect.height == 0)
				resultImageRoi = null;
		}

		if(resultImageRoi == null)
		{	// There is no ROI within the result image, thus I make the analysis within the whole picture
			intx = new double[w1 * h1];
			inty = new double[w1 * h1];
			lesx = new double[w1 * h1];
			lesy = new double[w1 * h1];

			for (y = 0; y < h1; y++)
			{
				for (x = 0; x < w1; x++)
				{
					pos = y * w1 + x;
//					vi1					= (int) (image1Processor.getPixelValue(x, y) * scatterPlotSize / depth1);
//					vi2					= (int) (image2Processor.getPixelValue(x, y) * scatterPlotSize / depth2);
					vi1					= (int) (image1Processor.getPixelValue(x, y) * scatterPlotSize / scatterPlotMax1);
					vi2					= (int) (image2Processor.getPixelValue(x, y) * scatterPlotSize / scatterPlotMax2);
					intx[y * w1 + x]	=		 image1Processor.getPixelValue(x, y);
					inty[y * w1 + x]	=		 image2Processor.getPixelValue(x, y);
					setMaskPixels();
				}
			}
		}
		else
		{	// There is a ROI within the result image, thus I make the analysis only within the ROI elements
			pointsInsideRoi = resultImageRoi.getContainedPoints();
			intx = new double[pointsInsideRoi.length];
			inty = new double[pointsInsideRoi.length];
			lesx = new double[pointsInsideRoi.length];
			lesy = new double[pointsInsideRoi.length];

			for (i = 0; i != pointsInsideRoi.length; i++)
			{
				if(pointsInsideRoi[i].x >= 0 && pointsInsideRoi[i].x < w1 && pointsInsideRoi[i].y >= 0 && pointsInsideRoi[i].y < h1)
				{
					pos		= pointsInsideRoi[i].y * w1 + pointsInsideRoi[i].x;
//					vi1		= (int) (image1Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) * scatterPlotSize / depth1);
//					vi2		= (int) (image2Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) * scatterPlotSize / depth2);
					vi1		= (int) (image1Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) * scatterPlotSize / scatterPlotMax1);
					vi2		= (int) (image2Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) * scatterPlotSize / scatterPlotMax2);
					intx[i]	=		 image1Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y);
					inty[i]	= 		 image2Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y);
					setMaskPixels();
				}
			}
		}
		lesx 					= Arrays.copyOf(lesx, counter);
		lesy 					= Arrays.copyOf(lesy, counter);

		colocMask				= new ByteProcessor(w1, h1, maskPixels);
		colocMask				.setBinaryThreshold();
		ts						= new ThresholdToSelection();
		colocMaskRoi			= ts.convert(colocMask);

		if (resultImageRoi		!= null)
		{
			if (resultImageRoi instanceof ShapeRoi)
				sr1				= (ShapeRoi)resultImageRoi.clone();
			else
				sr1				= new ShapeRoi(resultImageRoi);

			if (colocMaskRoi		!= null)
			{
				if (colocMaskRoi instanceof ShapeRoi)
					sr2				= (ShapeRoi)colocMaskRoi.clone();
				else
					sr2				= new ShapeRoi(colocMaskRoi);

				colocMaskRoi		= sr1.and(sr2);
			}
		}

		if(colocMaskRoi != null)
			colocMaskRoi		.setFillColor(Colors.decode("#EEFFFFFF", null));
//		resultImage				.setRoi(colocMaskRoi);
		resultImageOverlay		= resultImage.getOverlay();
		if (resultImageOverlay	== null)
		{
			resultImageOverlay	= new Overlay();
			resultImageOverlay	.addElement(colocMaskRoi);
		}
		else 
			resultImageOverlay	.set(colocMaskRoi, 0);
//			resultImageOverlay	.set(colocMaskRoi, resultImageOverlay.size() - 1);		Generated some bugs thus replaced the 'resultImageOverlay.size() - 1' by '0'
		resultImage				.setOverlay(resultImageOverlay);

		percentPixels = ((double) counter / (w1 * h1)) * 100.0;
		cf = new CurveFitter(lesx, lesy);
		cf.doFit(CurveFitter.STRAIGHT_LINE);
		cfParams = cf.getParams();

		String	output			= set_roi ? getResultsAsString(";") + ";" + colors[color].name : getResultsAsString(";");
//		if (write_results &&  IJ.getToolName() != "polygon")
//		if (write_results && (IJ.getToolName() == "rectangle" || IJ.getToolName() == "roundrect" || IJ.getToolName() == "rotrect" || IJ.getToolName() == "oval" || IJ.getToolName() == "ellipse" || IJ.getToolName() == "brush" || IJ.getToolName() == "freehand" || IJ.getToolName() == "polygon"))
		if (write_results && Toolbar.getInstance().getToolId() < 4)
		{
			ResultsWindow		= (TextWindow) WindowManager.getWindow(ResultsTitle);
			if(ResultsWindow == null)
			{
				ResultsWindow	= new TextWindow(ResultsTitle, ResultsHeadings, "", 1040, 300);
				ResultsWindow	.setIconImage		(icon);
			}
			ResultsWindow.append(output.replace(";", "\t"));
		}

//		if (set_roi &&  IJ.getToolName() != "polygon")
//		if (set_roi && (IJ.getToolName() == "rectangle" || IJ.getToolName() == "roundrect" || IJ.getToolName() == "rotrect" || IJ.getToolName() == "oval" || IJ.getToolName() == "ellipse" || IJ.getToolName() == "brush" || IJ.getToolName() == "freehand" || IJ.getToolName() == "polygon"))
		if (set_roi && Toolbar.getInstance().getToolId() < 4)
		{
			scatterPlotRoi		= scatterPlot.getRoi();
			scatterPlotRoi		.setStrokeColor(colors[color].color);
			rm					= RoiManager.getInstance();
			if (rm == null)
			{
				rm				= new RoiManager();
				rm				.setIconImage		(icon);
			}

			rm					.addRoi(scatterPlotRoi);
			rm					.rename(rm.getCount() - 1, colors[color].name);
			rm					.runCommand(scatterPlot, "Show All without labels");
			rm					.runCommand(resultImage, "Show None");	// Line added to get rid of the Rois within the RoiManager which are added by the line "rm.runCommand(i3,"Show All without labels");" in the case imResu is the selected window - And I don't know why!!!
			scatterPlot			.restoreRoi();
			scatterPlotRoi		= scatterPlot.getRoi();
			scatterPlotRoi		.setStrokeColor(Color.yellow);

			resultImageOverlay	= resultImage.getOverlay();
//			if (resultImageOverlay == null) resultImageOverlay = new Overlay();
			colocMaskRoi		.setFillColor(colors[color].color);
//			resultImage			.setRoi(colocMaskRoi);
			resultImageOverlay	.addElement(colocMaskRoi);
			resultImage			.setOverlay(resultImageOverlay);
//			resultImage			.killRoi();
			color				= color < 4 ? color + 1 : 0;
		}
		comparisonRunning		= false;

//		statusLabel.setPreferredSize(new Dimension(scatterPlotWindow.getWidth() -  73, statusLabel.getPreferredSize().height));
//		spaceString = String.format("%1$" +  Math.round(0.047 * scatterPlotWindow.getWidth() - 20) + "s", " ");

		if(show_checked == default_checked)
		{
			if(scatterPlotSize == 256)
				statusLabel.setText( "min1: "    + Math.round(minI1) +             "  max1: "    + Math.round(maxI1) +             "  min2: "    + Math.round(minI2) +             "  max2: "    + Math.round(maxI2));
			else
//				statusLabel.setText(" minI1: " + Math.round(minI1) + spaceString + "maxI1: " + Math.round(maxI1) + spaceString + "minI2: " + Math.round(minI2) + spaceString + "maxI2: " + Math.round(maxI2));
				statusLabel.setText(" Pearson: " + IJ.d2s(PearsonValue, precision) + spaceString + "minI1: " + Math.round(minI1) + spaceString + "maxI1: " + Math.round(maxI1) + spaceString + "minI2: " + Math.round(minI2) + spaceString + "maxI2: " + Math.round(maxI2));
		}
		else
		{
			String	str		= getStatusLabelString(1, nbChecked);
			int		size	= statusLabel.getPreferredSize().width - scatterPlotProcessor.getStringWidth(str) - 100;
			if (size / (5 * nbChecked) > 0)
				str = getStatusLabelString(size / (5 * nbChecked), nbChecked);
			statusLabel.setText(str);
		}

		return output;
	}

	private static String getStatusLabelString(int size, int nbChecked)
	{
		boolean	passed_first	= false;
		String	str				= "";
		String	separator		= nbChecked > 5 ? ":" : ": ";

		if((show_checked & show_Pearson)			!= 0)
		{
				passed_first	= true;
				str +=											" Pearson"		+ separator + IJ.d2s(PearsonValue					, precision);
		}
		if((show_checked & show_Overlap)			!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" Overlap"		+ separator + IJ.d2s(getOverlap(lesx, lesy)			, precision);
			else
			{
				passed_first	= true;
				str +=											" Overlap"		+ separator + IJ.d2s(getOverlap(lesx, lesy)			, precision);
			}
		}
		if((show_checked & show_k1)					!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" k1"			+ separator + IJ.d2s(getContrib(lesx, lesy)			, precision);
			else
			{
				passed_first	= true;
				str +=											" k1"			+ separator + IJ.d2s(getContrib(lesx, lesy)			, precision);
			}
		}
		if((show_checked & show_k2)					!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" k2"			+ separator + IJ.d2s(getContrib(lesy, lesx)			, precision);
			else
			{
				passed_first	= true;
				str +=											" k2"			+ separator + IJ.d2s(getContrib(lesy, lesx)			, precision);
			}
		}

		if((show_checked & show_M1)					!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" M1"			+ separator + IJ.d2s(getManders(intx, inty, minI1, minI2)	, precision);
			else
			{
				passed_first	= true;
				str +=											" M1"			+ separator + IJ.d2s(getManders(intx, inty, minI1, minI2)	, precision);
			}
		}
		if((show_checked & show_M2)					!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" M2"			+ separator + IJ.d2s(getManders(inty, intx, minI2, minI1)	, precision);
			else
			{
				passed_first	= true;
				str +=											" M2"			+ separator + IJ.d2s(getManders(inty, intx, minI2, minI1)	, precision);
			}
		}

		if((show_checked & show_M1_norm)			!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" M1_norm"		+ separator + IJ.d2s(getMandersNorm(intx, inty, minI1, minI2)	, precision);
			else
			{
				passed_first	= true;
				str +=											" M1_norm"		+ separator + IJ.d2s(getMandersNorm(intx, inty, minI1, minI2)	, precision);
			}
		}
		if((show_checked & show_M2_norm)			!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" M2_norm"		+ separator + IJ.d2s(getMandersNorm(inty, intx, minI2, minI1)	, precision);
			else
			{
				passed_first	= true;
				str +=											" M2_norm"		+ separator + IJ.d2s(getMandersNorm(inty, intx, minI2, minI1)	, precision);
			}
		}

		if((show_checked & show_Slope)				!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" slope"		+ separator + IJ.d2s(cfParams[1]					, precision);
			else
			{
				passed_first	= true;
				str +=											" slope"		+ separator + IJ.d2s(cfParams[1]					, precision);
			}
		}
		if((show_checked & show_Intercept)			!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" intercept"	+ separator + IJ.d2s(cfParams[0]					, precision);
			else
			{
				passed_first	= true;
				str +=											" intercept"	+ separator + IJ.d2s(cfParams[0]					, precision);
			}
		}
		if((show_checked & show_nb_pixels)			!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" nb_pixels"	+ separator + Math.round(counter);
			else
			{
				passed_first	= true;
				str +=											" nb_pixels"	+ separator + Math.round(counter);
			}
		}
		if((show_checked & show_percentage_pixels)	!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") + " %pixels"		+ separator + IJ.d2s(percentPixels				, precision);
			else
			{
				passed_first	= true;
				str +=											" %pixels"		+ separator + IJ.d2s(percentPixels				, precision);
			}
		}
		if((show_checked & show_min_I1)				!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" minI1"		+ separator + Integer.toString((int) minI1);
			else
			{
				passed_first	= true;
				str +=											" minI1"		+ separator + Integer.toString((int) minI1);
			}
		}
		if((show_checked & show_max_I1)				!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" maxI1"		+ separator + Integer.toString((int) maxI1);
			else
			{
				passed_first	= true;
				str +=											" maxI1"		+ separator + Integer.toString((int) maxI1);
			}
		}
		if((show_checked & show_min_I2)				!= 0)
		{
			if(passed_first)
				str += String.format("%1$" + size + "s", " ") +	" minI2"		+ separator + Integer.toString((int) minI2);
			else
			{
				passed_first	= true;
				str +=											" minI2"		+ separator + Integer.toString((int) minI2);
			}
		}
		if((show_checked & show_max_I2)				!= 0)
			str += String.format("%1$" + size + "s", " ") +		" maxI2"		+ separator + Integer.toString((int) maxI2);

		return str;
	}

	static void setMaskPixels()
	{
		if (scatterPlotRoi.contains(vi1 + xOffset, scatterPlotSize - vi2 + yOffset))
		{
			maskPixels	[pos]		= (byte) 0;
			lesx		[counter]	= vi1;
			lesy		[counter]	= vi2;
			counter++;
		}
		else
			maskPixels	[pos]		= (byte) 255;
	}

	static double getOverlap(double[] d1, double[] d2)
	{
		double  sum  = 0.d;
		double ssum1 = 0.d;
		double ssum2 = 0.d;

		for (int i = 0; i < d1.length; i++)
		{
			sum   += d1[i] * d2[i];
			ssum1 += d1[i] * d1[i];
			ssum2 += d2[i] * d2[i];
		}
		return sum / ((double) Math.sqrt(ssum1 * ssum2));
	}

	static double getContrib(double[] d1, double[] d2)
	{
		double  sum  = 0.d;
		double ssum1 = 0.d;

		for (int i = 0; i < d1.length; i++)
		{
			sum   += d1[i] * d2[i];
			ssum1 += d1[i] * d1[i];
		}
		return sum / ((double) ssum1);
	}

	static double getManders(double[] d1, double[] d2, double threshold1, double threshold2)
	{
		double sum1 = 0.d;
		double sum2 = 0.d;

		for (int i = 0; i < d1.length; i++)
		{
			if (d1[i] > threshold1)
			{
				if (d2[i] > threshold2)
					sum1 += d1[i];
				sum2 += d1[i];
			}
		}
		return sum1 / ((double) sum2);
	}

	static double getMandersNorm(double[] d1, double[] d2, double threshold1, double threshold2)
	{
		double sum1 = 0.d;
		double sum2 = 0.d;

		for (int i = 0; i < d1.length; i++)
		{
			if (d1[i] > threshold1)
			{
				if (d2[i] > threshold2)
					sum1 += 1;
				sum2 += 1;
			}
		}
		return sum1 / ((double) sum2);
	}

	/* methods from G.Chinga */

	static double getR(double[] d1, double[] d2)
	{
		double t1;
		double t2;
		double sum		= 0.d;
/*
		double xMean	= getMean	(		d1);
		double yMean	= getMean	(		d2);
		double xStd		= getStd	(xMean,	d1);
		double yStd		= getStd	(yMean,	d2);
*/
				xMean	= getMean	(		d1);
				yMean	= getMean	(		d2);
				xStd	= getStd	(xMean,	d1);
				yStd	= getStd	(yMean,	d2);

		for (int i = 0; i < d1.length; i++)
		{
			t1	= (d1[i] - xMean) / xStd;
			t2	= (d2[i] - yMean) / yStd;
			sum+= t1 * t2;
		}
		return sum / (d1.length - 1);
	}

	static double sqr(double x)
	{
		return x * x;
	}

	static double getMean(double[] dataset)
	{
		double mValue = 0.d;

		for (int j = 0; j < dataset.length; j++)
			mValue += dataset[j];

		return mValue / dataset.length;
	}

	static double getStd(double mValue, double[] dataset)
	{
		double sValue = 0.d;

		if (dataset.length == 1)
			return sValue;
		else
		{
			for (int j = 0; j < dataset.length; j++)
				sValue += sqr(mValue - dataset[j]);

			return Math.sqrt(sValue / (dataset.length - 1));
		}
	}

	/* end methods from G.Chinga */

	/* methods from ij.gui.Plot */

	private static void build_plot_for_scatter_plot()
	{
		FontMetrics fm			= scatterPlotProcessor.getFontMetrics();
		int fontAscent			= fm.getAscent();
		int MIN_X_GRIDSPACING	= 45;				// minimum distance between grid lines or ticks along x at plot width 0
		int MIN_Y_GRIDSPACING	= 30;				// minimum distance between grid lines or ticks along y at plot height 0
		int LEFT_MARGIN			= 47;
		int maxIntervals		= 12;				// maximum number of intervals between ticks or grid lines
		int tickLength			= 7;				// length of major ticks
		int minorTickLength		= 3;				// length of minor ticks
		int yOfXAxisNumbers		= scatterPlotSize + 49;
		int x1					= xOffset - 2;
		int x2					= xOffset + 2 + scatterPlotSize;
		int y1					= yOffset - 2;
		int y2					= yOffset + 2 + scatterPlotSize;
		int i1, i2, y, digits;
		double  xScale, yScale, xStep, yStep;
		double v;
		String str;

		scatterPlotProcessor.setColor(255);

		// draw plot legends
		scatterPlotProcessor.drawString(titles[i1Index], xOffset + (scatterPlotSize - scatterPlotProcessor.getStringWidth(titles[i1Index])) / 2, scatterPlotSize + windowOffset - yOffset + scatterPlotProcessor.getFontMetrics().getHeight());
		scatterPlotProcessor.drawString(titles[i1Index], xOffset + (scatterPlotSize - scatterPlotProcessor.getStringWidth(titles[i1Index])) / 2, scatterPlotSize + windowOffset - yOffset + scatterPlotProcessor.getFontMetrics().getHeight());
		                     drawYLabel(titles[i2Index], yOffset, yOffset, scatterPlotSize);

		// draw plot contour
		scatterPlotProcessor.drawRect(xOffset - 1, yOffset - 1, scatterPlotSize + 3, scatterPlotSize + 3);

		// Along X Axis
		xScale = scatterPlotSize / (scatterPlotMax1 - scatterPlotMin1);
		xStep  = Math.abs((scatterPlotMax1 - scatterPlotMin1) * Math.max(1.0 / maxIntervals, (double) MIN_X_GRIDSPACING / scatterPlotSize + 0.06));	// the smallest allowable step
		xStep  = niceNumber(xStep);
		i1     = (int) Math.ceil (scatterPlotMin1 / xStep - 1.e-10);
		i2     = (int) Math.floor(scatterPlotMax1 / xStep + 1.e-10);
		digits = getDigits(scatterPlotMin1, scatterPlotMax1, xStep, 7);
		for (int i = 0; i <= (i2 - i1); i++)
		{
			v = (i + i1) * xStep;
			x = (int) Math.round((v - scatterPlotMin1) * xScale) + xOffset - 1;
			// X major ticks
			scatterPlotProcessor.drawLine(x, y1, x, y1 - tickLength);
			scatterPlotProcessor.drawLine(x, y2, x, y2 + tickLength);
			// X numbers
			str = IJ.d2s(v, digits);
			scatterPlotProcessor.drawString(str, x - scatterPlotProcessor.getStringWidth(str) / 2, yOfXAxisNumbers);
		}
		// X minor ticks
		xStep	= niceNumber(xStep * 0.19);
		i1		= (int) Math.ceil (scatterPlotMin1 / xStep - 1.e-10);
		i2		= (int) Math.floor(scatterPlotMax1 / xStep + 1.e-10);
		for (int i = i1; i <= i2; i++)
		{
			v = i * xStep;
			x = (int) Math.round((v - scatterPlotMin1) * xScale) + xOffset - 1;
			scatterPlotProcessor.drawLine(x, y1, x, y1 - minorTickLength);
			scatterPlotProcessor.drawLine(x, y2, x, y2 + minorTickLength);
		}

		// Along Y Axis
		yScale	= scatterPlotSize / (scatterPlotMax2 - scatterPlotMin2);
		yStep	= Math.abs((scatterPlotMax2 - scatterPlotMin2) * Math.max(1.0 / maxIntervals, (double) MIN_Y_GRIDSPACING / scatterPlotSize + 0.06)); // the smallest allowable step
		yStep	= niceNumber(yStep);
		i1		= (int) Math.ceil (scatterPlotMin2 / yStep - 1.e-10);
		i2		= (int) Math.floor(scatterPlotMax2 / yStep + 1.e-10);
		digits	= getDigits(scatterPlotMin2, scatterPlotMax2, yStep, 5);
		for (int i = i1; i <= i2; i++)
		{
			v = yStep == 0 ? scatterPlotMin2 : i * yStep;
			y = yOffset + scatterPlotSize + 1 - (int) Math.round((v - scatterPlotMin2) * yScale);
			// Y major ticks
			scatterPlotProcessor.drawLine(x1, y, x1 - tickLength, y);
			scatterPlotProcessor.drawLine(x2, y, x2 + tickLength, y);
			// Y numbers
			str = IJ.d2s(v, digits);
			scatterPlotProcessor.drawString(str, LEFT_MARGIN - scatterPlotProcessor.getStringWidth(str), y	+ fontAscent * 2 / 3);
		}

		// Y minor ticks
		yStep	= 		niceNumber	(yStep * 0.19);
		i1		= (int)	Math.ceil	(scatterPlotMin2 / yStep - 1.e-10);
		i2		= (int)	Math.floor	(scatterPlotMax2 / yStep + 1.e-10);
		for (int i = i1; i <= i2; i++)
		{
			v = i * yStep;
			y = yOffset + scatterPlotSize + 1 - (int) Math.round((v - scatterPlotMin2) * yScale);
			scatterPlotProcessor.drawLine(x1, y, x1 - minorTickLength, y);
			scatterPlotProcessor.drawLine(x2, y, x2 + minorTickLength, y);
		}
	}

	// Number of digits to display the number n with resolution 'resolution';
	// (if n is integer and small enough to display without scientific notation,
	// no decimals are needed, irrespective of 'resolution')
	// Scientific notation is used for more than 'maxDigits' (must be >=3), and indicated
	// by a negative return value
	static int getDigits(double n, double resolution, int maxDigits)
	{
		if (n == Math.round(n) && Math.abs(n) < Math.pow(10, maxDigits - 1) - 1) // integers and not too big
			return 0;
		else
			return getDigits2(n, resolution, maxDigits);
	}

	// Number of digits to display the range between n1 and n2 with resolution 'resolution';
	// Scientific notation is used for more than 'maxDigits' (must be >=3), and indicated
	// by a negative return value
	static int getDigits(double n1, double n2, double resolution, int maxDigits)
	{
		if (n1 == 0 && n2 == 0) return 0;
		return getDigits2(Math.max(Math.abs(n1), Math.abs(n2)), resolution,	maxDigits);
	}

	static int getDigits2(double n, double resolution, int maxDigits)
	{
		int log10ofN = (int) Math.floor(Math.log10(Math.abs(n)) + 1e-7);
		int digits = resolution != 0 ? -(int) Math.floor(Math.log10(Math.abs(resolution)) + 1e-7) : Math.max(0, -log10ofN + maxDigits - 2);
		int sciDigits = -Math.max((log10ofN + digits), 1);
		if      (digits < -2 && log10ofN >= maxDigits)    digits = sciDigits; // scientific notation for large numbers
		else if (digits < 0)                              digits = 0;
		else if (digits > maxDigits - 1 && log10ofN < -2) digits = sciDigits; // scientific notation for small numbers
		return digits;
	}

	// Returns the smallest "nice" number >= v. "Nice" numbers are .. 0.5, 1, 2, 5, 10, 20 ...
	static double niceNumber(double v)
	{
		double base = Math.pow(10, Math.floor(Math.log10(v) - 1.e-6));
		if		(v > 5.0000001 * base) return 10 * base;
		else if	(v > 2.0000001 * base) return  5 * base;
		else                           return  2 * base;
	}

	// Vertical text for y axis label
	private static void drawYLabel(String yLabel, int xRight, int yFrameTop, int frameHeight)
	{
		if (yLabel.equals(""))
			return;
		FontMetrics fm = scatterPlotProcessor.getFontMetrics();
		int w = scatterPlotProcessor.getStringWidth(yLabel);
		int h = fm.getHeight();
		ImageProcessor label = new ByteProcessor(w, h);
		label.setColor(Color.white);
		label.drawString(yLabel, 0, h);
		label = label.rotateLeft();
		int y2 = yFrameTop + (frameHeight - scatterPlotProcessor.getStringWidth(yLabel)) / 2;
		if (y2 < yFrameTop)
			y2 = yFrameTop;
		int x2 = Math.max(xRight - h, 0);
		scatterPlotProcessor.insert(label, x2, y2);
	}
	/* end methods from ij.gui.Plot */

	private void setScatterPlotRoiSetting()
	{
		boolean[] selectedItemsValues = { (show_checked & show_Pearson) != 0, (show_checked & show_Overlap) != 0, (show_checked & show_k1) != 0, (show_checked & show_k2) != 0, (show_checked & show_M1) != 0, (show_checked & show_M2) != 0, (show_checked & show_M1_norm) != 0, (show_checked & show_M2_norm) != 0, (show_checked & show_Slope) != 0, (show_checked & show_Intercept) != 0, (show_checked & show_nb_pixels) != 0, (show_checked & show_percentage_pixels) != 0, (show_checked & show_min_I1) != 0, (show_checked & show_max_I1) != 0, (show_checked & show_min_I2) != 0, (show_checked & show_max_I2) != 0 };
		if(setScatterPlotRoiLimits())
			setScatterPlotRoi(minI1, maxI1, minI2, maxI2);

		gd						= new GenericDialog("ScatterPlot settings");
		gd.setIconImage			(icon);
		gd.addMessage			("ScatterPlot graph limits"	, new Font("SansSerif", Font.PLAIN, 15), Color.BLUE);
		gd.addNumericField		("min_I1", scatterPlotMin1	, 0);
		gd.addNumericField		("max_I1", scatterPlotMax1	, 0);
		gd.addNumericField		("min_I2", scatterPlotMin2	, 0);
		gd.addNumericField		("max_I2", scatterPlotMax2	, 0);
		gd.setInsets			(-105, 0, 0);
		gd.addImage				(insertImp2);
		gd.addMessage			("ScatterPlot ROI limits"	, new Font("SansSerif", Font.PLAIN, 15), Color.BLUE);
		gd.addNumericField		("min_I1", minI1			, 0);
		gd.addNumericField		("max_I1", maxI1			, 0);
		gd.addNumericField		("min_I2", minI2			, 0);
		gd.addNumericField		("max_I2", maxI2			, 0);
		gd.setInsets			( -105, 0, 0);
		gd.addImage				(insertImp3);
		gd.addMessage			("Live display"				, new Font("SansSerif", Font.PLAIN, 15), Color.BLUE);
		gd.addMessage			("It is recommand to not choose more than\n   5 items in order to avoid overlapping"	, new Font("SansSerif", Font.PLAIN, 15), Color.RED);
		gd.addCheckboxGroup		(8, 2, selectedItemsLabels, selectedItemsValues);
		gd.addNumericField		("Decimal places (0-9):", precision, 0, 2, "");
		gd.enableYesNoCancel	();
		gd.enableYesNoCancel	("OK", "Reset");

		checkboxes				= (Checkbox	[])	(gd.getCheckboxes	().toArray(new Checkbox	[gd.getCheckboxes	().size()]));
		for(i = 0; i < checkboxes.length; i++)
			checkboxes[i].addItemListener(this);

		dlgItems				= gd.getComponents();
		if(nbChecked <= 5)
			dlgItems[21]			.setVisible( false );
		gd.pack();

		gd.showDialog();

		if (gd.wasCanceled())
			return;

		if (gd.wasOKed())
		{
			scatterPlotMin1			= gd.getNextNumber();
			scatterPlotMax1			= gd.getNextNumber();
			scatterPlotMin2			= gd.getNextNumber();
			scatterPlotMax2			= gd.getNextNumber();

			minI1					= gd.getNextNumber();
			maxI1					= gd.getNextNumber();
			minI2					= gd.getNextNumber();
			maxI2					= gd.getNextNumber();

			show_checked			= 0;
			if(gd.getNextBoolean())	show_checked |= show_Pearson;
			if(gd.getNextBoolean())	show_checked |= show_Overlap;
			if(gd.getNextBoolean())	show_checked |= show_k1;
			if(gd.getNextBoolean())	show_checked |= show_k2;
			if(gd.getNextBoolean())	show_checked |= show_M1;
			if(gd.getNextBoolean())	show_checked |= show_M2;
			if(gd.getNextBoolean())	show_checked |= show_M1_norm;
			if(gd.getNextBoolean())	show_checked |= show_M2_norm;
			if(gd.getNextBoolean())	show_checked |= show_Slope;
			if(gd.getNextBoolean())	show_checked |= show_Intercept;
			if(gd.getNextBoolean())	show_checked |= show_nb_pixels;
			if(gd.getNextBoolean())	show_checked |= show_percentage_pixels;
			if(gd.getNextBoolean())	show_checked |= show_min_I1;
			if(gd.getNextBoolean())	show_checked |= show_max_I1;
			if(gd.getNextBoolean())	show_checked |= show_min_I2;
			if(gd.getNextBoolean())	show_checked |= show_max_I2;

			precision				= (int) gd.getNextNumber();
		}
		else
		{
			scatterPlotMin1			= minI1					= min1;
			scatterPlotMax1			= maxI1					= max1;
			scatterPlotMin2			= minI2					= min2;
			scatterPlotMax2			= maxI2					= max2;
		}

		scatterPlotProcessor		.setColor(Color.black);
		scatterPlotProcessor		.resetRoi();
		scatterPlotProcessor		.fill();
		setScatterPlotGraphLimits	();
		build_plot_for_scatter_plot	();
		rebuild_scatter_plot		();
		setScatterPlotRoi			(minI1, maxI1, minI2, maxI2);
	}

	public void actionPerformed(ActionEvent e)
	{
		try
		{
			Object b = e.getSource();
			if (b == set)
				setScatterPlotRoiSetting();
		}
		catch (Exception ex)
		{
			IJ.handleException(ex);
		}
	}

	public void itemStateChanged(ItemEvent e)
	{
		int i;
		nbChecked = 0;

		for(i = 0; i < checkboxes.length; i++)
			if(checkboxes[i].getState())
				nbChecked++;
		if(nbChecked > 5)
			dlgItems[21].setVisible( true );
		else
			dlgItems[21].setVisible( false );
		gd.pack();
	}

	public void imageOpened(ImagePlus imp)			{}

	public void imageUpdated(ImagePlus imp)			{}

	public void imageClosed(ImagePlus imp)
	{
/*
		if (imp == this.scatterPlot)
		{
			scatterPlotRoi			.removeRoiListener				(this);
			scatterPlot.getCanvas()	.removeMouseListener			(this);
			scatterPlot.getCanvas()	.removeKeyListener				(this);
			scatterPlotWindow		.removeKeyListener				(this);
		}
		if (imp == this.resultImage)
		{
			resultImageRoi			.removeRoiListener				(this);
			resultImage.getCanvas()	.removeMouseListener			(this);
			resultImage.getCanvas()	.removeMouseMotionListener		(this);
			Prefs.blackBackground	= previousblackBackgroundState;
		}
*/
		Prefs.blackBackground	= previousblackBackgroundState;
	}

	public synchronized void roiModified(ImagePlus imp, int id)
	{
		if(!comparisonRunning)
		{
			if(id == CREATED && !mouseInsideResultImage && !mouseInsideScatterPlot)
			{
				if (imp == scatterPlot)
				{
					comparison(false, false);
					scatterPlot.draw();
				}
				else if (imp == resultImage)
				{
					rebuild_scatter_plot();
					comparison(false, false);
				}
			}
			else if(imp == scatterPlot)
			{
				if (id == CREATED || id == MODIFIED || id == MOVED || id == COMPLETED)
				{
					scatterPlotModified = true;
					if (bgThread == null)
					{
						bgThread = new Thread(this, "scatterPlot update");
						bgThread.setPriority(Math.max(bgThread.getPriority() - 3, Thread.MIN_PRIORITY));
						bgThread.start();
					}
					else
						notify();
				}
//				else if (id == CREATED)
//				{	
//					comparison(false, false);
//					scatterPlot.draw();
//				}
			}
			else if(imp == resultImage)
			{
				if (id == CREATED || id == DELETED || id == MODIFIED || id == MOVED || id == COMPLETED)
				{
					resultImageModified = true;
					if (bgThread == null)
					{
						bgThread = new Thread(this, "resultImage update");
						bgThread.setPriority(Math.max(bgThread.getPriority() - 3, Thread.MIN_PRIORITY));
						bgThread.start();
					}
					else
						notify();
				}
//				else if (id == CREATED)
//				{
//					rebuild_scatter_plot();
//					comparison(false, false);
//				}
			}
		}
	}

	public void mouseClicked(MouseEvent evt)
	{
//		clickCount = 0;

		if (evt.getButton() == MouseEvent.BUTTON1 && clickInsideRoi(evt))
		{
//			if ((evt.getModifiers() & ActionEvent.CTRL_MASK) == ActionEvent.CTRL_MASK)
			if (evt.isControlDown())
				comparison(true, true);
			else
				comparison(true, false);
/*
			// Code implementing a double click within the scatterPlot window
			// which became unusable after the 1.53c update version
			if (evt.getClickCount() == 2)
				doubleClick = true;

			timer = new Timer(multiClickInterval, new ActionListener()
			{
				public void actionPerformed(ActionEvent e)
				{
					if (doubleClick)
					{
						clickCount++;
						if (clickCount == 2)
						{
							comparison(true, true);
							clickCount = 0;
							doubleClick = false;
						}
					}
					else
						comparison(true, false);
				}
			});
			timer.setRepeats(false);
			timer.start();
			if (evt.getID() == MouseEvent.MOUSE_RELEASED)
				timer.stop();
*/
		}
	}

	private boolean clickInsideRoi(MouseEvent evt)
	{
			 if (mouseInsideResultImage)
		{
			if(resultImage.getRoi().contains(resultImage.getCanvas().offScreenX(evt.getX()), resultImage.getCanvas().offScreenY(evt.getY())))
				return true;
			else
				return false;
		}
		else if (mouseInsideScatterPlot)
		{
			if(scatterPlot.getRoi().contains(scatterPlot.getCanvas().offScreenX(evt.getX()), scatterPlot.getCanvas().offScreenY(evt.getY())))
				return true;
			else
				return false;
		}
		return false;
	}

	public void mousePressed(MouseEvent evt) {}

	public void mouseExited(MouseEvent evt)
	{
        icc = (ImageCanvas) evt.getSource();
			 if (icc.getImage() == this.resultImage)
			mouseInsideResultImage = false;
		else if (icc.getImage() == this.scatterPlot)
			mouseInsideScatterPlot = false;
	}

	public void mouseEntered(MouseEvent evt)
	{
        icc = (ImageCanvas) evt.getSource();
			 if (icc.getImage() == this.resultImage)
			mouseInsideResultImage = true;
		else if (icc.getImage() == this.scatterPlot)
			mouseInsideScatterPlot = true;
	}

	public void mouseReleased(MouseEvent evt)
	{
		if (bgThread != null)
			bgThread.interrupt();
		bgThread = null;
		if (scatterPlotModified)
		{
			scatterPlotModified		= false;
			comparison(false, false);
			scatterPlot.draw();
		}
		else if (resultImageModified)
		{
			resultImageModified		= false;
			rebuild_scatter_plot();
			comparison(false, false);
		}
	}

	public void mouseMoved(MouseEvent evt)
	{
//		if (mouseInsideResultImage && evt.getModifiers() == ActionEvent.CTRL_MASK)
//		if (mouseInsideResultImage && evt.isControlDown())
		if (mouseInsideResultImage && evt.isShiftDown())
		{
			scatterPlotRoi	= scatterPlot.getRoi();
			if(scatterPlotRoi == null)
				scatterPlot.setRoi(new Rectangle(50 + xOffset, 50 + yOffset, 150, 150));
			coord			= scatterPlotRoi.getBounds();
			roiWidth		= coord.width;
			roiHeight		= coord.height;
			scatterPlotRoi	.setLocation(         Math.round((image1Processor.getPixelValue(resultImage.getCanvas().offScreenX(evt.getX()), resultImage.getCanvas().offScreenY(evt.getY())) * scatterPlotSize / scatterPlotMax1) + xOffset - roiWidth  / 2),
								scatterPlotSize - Math.round((image2Processor.getPixelValue(resultImage.getCanvas().offScreenX(evt.getX()), resultImage.getCanvas().offScreenY(evt.getY())) * scatterPlotSize / scatterPlotMax2) - yOffset + roiHeight / 2));
			scatterPlot		.killRoi();
			scatterPlot		.restoreRoi();
			comparison(false, false);
/*
			i3.setRoi(Math.round(image1Processor.getPixelValue(canvasResu.offScreenX(evt.getX()) , canvasResu.offScreenY(evt.getY())) + xOffset - widthR  / 2)
			  , scatterPlotSize - Math.round(image2Processor.getPixelValue(canvasResu.offScreenX(evt.getX()) , canvasResu.offScreenY(evt.getY())) - yOffset + heightR / 2)
			  , widthR, heightR);
*/
		}
	}

	public void mouseDragged(MouseEvent e) {}

	public void keyPressed(KeyEvent e)
	{
		int keyCode = e.getKeyCode();
//		e.consume();

		if (keyCode == e.VK_G)	// g, q or u
		{
			setScatterPlotRoiSetting();
		}
		else if (keyCode == KeyEvent.VK_NUMPAD4 || keyCode == KeyEvent.VK_NUMPAD6)
		{
			long	[] hist1 = image1Statistics.getHistogram();
			double	[] xval1 = new double[image1Statistics.nBins];
			double	[] yval1 = new double[image1Statistics.nBins];
			for (i = 0; i != image1Statistics.nBins; i++)
			{
				xval1[i] = i * (max1 - min1) / image1Statistics.nBins;
				yval1[i] = (double) hist1[i];
			}
			CurveFitter cf1 = new CurveFitter(xval1, yval1);
			cf1.doFit(CurveFitter.GAUSSIAN);
			Fitter.plot(cf1);
			double[] fitParam1 = cf1.getParams();
//			IJ.log(String.valueOf(fitParam1[2]));
//			rt = new ResultsTable();
//			rt.incrementCounter();
//			rt.addValue(titles[i2Index], fitParam1[2]);
//			rt.show(titles[i2Index]);
			StringSelection selection = new StringSelection(String.valueOf(fitParam1[2]));
			Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
			clipboard.setContents(selection, selection);
		}
		else if (keyCode == KeyEvent.VK_NUMPAD2	|| keyCode == KeyEvent.VK_NUMPAD8)
		{
			long	[] hist2 = image2Statistics.getHistogram();
			double	[] xval2 = new double[image2Statistics.nBins];
			double	[] yval2 = new double[image2Statistics.nBins];
			for (i = 0; i != image2Statistics.nBins; i++)
			{
				xval2[i] = i * (max2 - min2) / image2Statistics.nBins;
				yval2[i] = (double) hist2[i];
			}
			CurveFitter cf2 = new CurveFitter(xval2, yval2);
			cf2.doFit(CurveFitter.GAUSSIAN);
			Fitter.plot(cf2);
			double[] fitParam2 = cf2.getParams();
//			IJ.log(String.valueOf(fitParam2[2]));
//			rt = new ResultsTable();
//			rt.incrementCounter();
//			rt.addValue(titles[i1Index], fitParam2[2]);
//			rt.show(titles[i1Index]);
			StringSelection selection = new StringSelection(String.valueOf(fitParam2[2]));
			Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
			clipboard.setContents(selection, selection);
		}
	}

	public void keyReleased(KeyEvent e)
	{
		if (bgThread != null)
			bgThread.interrupt();
		bgThread = null;
		if (scatterPlotModified)
		{
			scatterPlotModified		= false;
			comparison(false, false);
			scatterPlot.draw();
		}
		else if (resultImageModified)
		{
			resultImageModified		= false;
			rebuild_scatter_plot();
			comparison(false, false);
		}
	}

	public void keyTyped(KeyEvent e) {}

	private void defineColors()
	{
		color		= 0;
		colors		= new ColorDefinition[5];
		colors[0]	= new ColorDefinition("red"    , Color.red    , 255,   0,   0);
		colors[1]	= new ColorDefinition("green"  , Color.green  ,   0, 255,   0);
		colors[2]	= new ColorDefinition("blue"   , Color.blue   ,   0,   0, 255);
		colors[3]	= new ColorDefinition("magenta", Color.magenta, 255,   0, 255);
		colors[4]	= new ColorDefinition("cyan"   , Color.cyan   ,   0, 255, 255);
	}

	class ColorDefinition
	{
		public int r, g, b;
		public String name;
		public java.awt.Color color;

		ColorDefinition(String name, java.awt.Color color, int r, int g, int b)
		{
			this.name = name;
			this.color = color;
			this.r = r;
			this.g = g;
			this.b = b;
		}
	}

	public static String getResultsAsString(String separator)
	{
		PearsonValue			= Double.isNaN(getR(lesx, lesy))			? 0										: getR(lesx, lesy);
		PearsonValueAsString	= Math.abs(PearsonValue) < 1e-3				? String.format("%.7E", PearsonValue)	: IJ.d2s(PearsonValue, 8);
		if (resultImage.getRoi() == null)
			resultImageRoiName	= "-";
		else if (resultImage.getRoi().getName()	== null)
			resultImageRoiName	= "-";
		else
			resultImageRoiName	= resultImage.getRoi().getName();

		return	  resultImage			.getImageStack().getSliceLabel(1)					+ separator
				+ resultImage			.getImageStack().getSliceLabel(2)					+ separator
				+ resultImageRoiName														+ separator
				+ PearsonValueAsString														+ separator
				+ IJ.d2s			(	xMean										, 8	)	+ separator
				+ IJ.d2s			(	yMean										, 8	)	+ separator
				+ IJ.d2s			(	xStd										, 8	)	+ separator
				+ IJ.d2s			(	yStd										, 8	)	+ separator
				+ IJ.d2s			(	getOverlap		(lesx, lesy)				, 8	)	+ separator
				+ IJ.d2s			(	getContrib		(lesx, lesy)				, 8	)	+ separator
				+ IJ.d2s			(	getContrib		(lesy, lesx)				, 8	)	+ separator
				+ IJ.d2s			(	getManders		(intx, inty, minI1, minI2)	, 8	)	+ separator
				+ IJ.d2s			(	getManders		(inty, intx, minI2, minI1)	, 8	)	+ separator
				+ IJ.d2s			(	getMandersNorm	(intx, inty, minI1, minI2)	, 8	)	+ separator
				+ IJ.d2s			(	getMandersNorm	(inty, intx, minI2, minI1)	, 8	)	+ separator
				+ IJ.d2s			(	cfParams[1]									, 5	)	+ separator
				+ IJ.d2s			(	cfParams[0]									, 5	)	+ separator
				+ Integer.toString	(			counter									)	+ separator
				+ IJ.d2s			(	percentPixels								, 4	)	+ separator
				+ Integer.toString	((int)	(	minI1	)								)	+ separator
				+ Integer.toString	((int)	(	maxI1	)								)	+ separator
				+ Integer.toString	((int)	(	minI2	)								)	+ separator
				+ Integer.toString	((int)	(	maxI2	)								)	+ separator
				+ IJ.d2s			(	getMean(lesx) * scatterPlotMax1 / 255	, 5		)	+ separator
				+ IJ.d2s			(	getMean(lesy) * scatterPlotMax2 / 255	, 5		)	;
	}

	public void showAbout()
	{
		String	aboutMessage = 	"Colocalization_finder\n\n" +
								"Required version:\tImageJ 1.52p01 or higher\n" +
								"Runing    version:\tImageJ " + IJ.getFullVersion() + "\n\n" +
								"Version 1.7\n" +
								"\tAuthor\t: Philippe Carl\n" +
								"\tEmail\t: philippe.carl at unistra dot fr\n" +
								"\tDate\t: 18/03/2023\n\n" +
								"\t- Addition of a ScatterPlot_ROI_name column within the Colocalization Finder Results window\n\n" +
								"Version 1.6\n" +
								"\tAuthor\t: Philippe Carl\n" +
								"\tDate\t: 06/12/2022\n\n" +
								"\t- Possibility to choose the size of the scatter plot upon start of the plugin\n" +
								"\t- Addition of a label panel at the bottom of the scatterPlot picture displaying the limits of the scatterPlot\n" +
								"\t  Roi selection (or other parameters upon selection)\n" +
								"\t- Addition of a \"Set\" button at the bottom left of the scatterPlot picture allowing so set the limits of the\n" +
								"\t  scatterPlot graph and/or of the scatterPlot Roi  and/or choosing the displayed parameters within the\n" +
								"\t  label panel at the bottom of the scatterPlot (the 'g' key gives the same features)\n" +
								"\t- Addition of the Manders coefficients (M1, M2 and M1_norm, M2_norm) calculation\n" +
								"\t- The possibility to set ROIs with given colors with a mouse double click has been erased (due to the\n" +
								"\t  ImageJ 1.53c 26 June 2020 update) and replaced by a Ctrl + mouse click user action\n\n" +
								"Version 1.5\n" +
								"\tAuthor\t: Philippe Carl\n" +
								"\tDate\t: 12/15/2019\n\n" +
								"\t- Possibility to add a selection within the Composite picture to restric the analysis a the given selection\n" +
								"\t- Addition of synchronized background thread for smoothly updating the calculations on the fly\n\n" +
								"Version 1.4\n" +
								"\tAuthor\t: Philippe Carl\n" +
								"\tDate\t: 10/20/2019\n\n" +
								"\t- Addition of scripting possibilities through plugin or macro programming\n" +
								"\t- The colocalization calculations are performed using double parameters instead of float\n" +
								"\t- Possibility to reduce the analysis to a ROI within the composite picture\n\n" +
								"Version 1.3\n" +
								"\tAuthor\t: Philippe Carl\n" +
								"\tDate\t: 4/30/2016\n\n" +
								"\t- Replacement of the deprecated functions (getBoundingRect, IJ.write) by the new ones\n" +
								"\t- Extension of the plugin for whatever picture dynamics\n" +
								"\t- Addition of a plot (with legends, ticks (minor and major), labels) within the scatter plot\n" +
 								"\t- The selected points within the overlay picture are updated as soon as the ROI in the scatter plot is\n" +
 								"\t  modified or dragged over\n" +
								"\t- Possibility to move the ROI position (within the scatter plot) from the mouse position within the overlay\n" +
								"\t  picture\n" +
								"\t- Possibility to set ROIs with given colors with a mouse double click\n" +
								"\t- Possibility to generate the x or y histogram with a Gaussian fit in order to extract the histogram\n" +
								"\t  maximum position by using the numeric pad 4/6 or 2/8 keys\n\n" +
								"Version 1.2\n" +
								"\tAuthors : C. Laummonerie & J. Mutterer\n" +
								"\t- Rewrote the mask overlay part, now faster\n" +
								"\t- Made the scatterplot selection possible with any kind of closed selections after several requests\n" +
								"\t- The ratio bars are now overlaid on a separte layer, so that you still can read the pixel info behind\n" +
								"\t  these bars\n" +
								"\t- Fixed the Fire LUT issue (LUT was not always applied)\n\n" +
								"Version 1.2\n" +
								"\tAuthors: C. Laummonerie & J. Mutterer\n" +
								"\t\t  written for the IBMP-CNRS Strasbourg(France)\n" +
								"\tEmail\t: jerome.mutterer at ibmp-ulp.u-strasbg.fr\n" +
								"\tDescription :  This plugin displays a correlation diagram for two images (8bits, same size). Drawing a\n" +
								"\trectangular selection on this diagram allows you to highlight corresponding pixels on a RGB overlap of\n" +
								"\tthe original images, and if selected, on a 3rd image.\n" +
								"\tAnalysis can be restricted to pixels having values with a minimum ratio. Selection settings are logged\n" +
								"\tto a results window.\n" +
								"\tLarge parts of this code were taken from Wayne Rasband, Pierre Bourdoncle and Gary Chinga.\n\n\n" +
								"This program is free software; you can redistribute it and/or modify it under the terms of the GNU General\n" +
								"Public License as published by the Free Software Foundation; either version 2 of the License, or (at your\n" +
								"option) any later version.\n\n" +
								"This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the\n" +
								"implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.\n\n" +
								"See the GNU General Public License for more details.\n\n" +
								"You should have received a copy of the GNU General Public License along with this program; if not, write to\n" +
								"the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA\n";

		gd = new GenericDialog	("Colocalization_finder - About...");
		gd.setIconImage			(icon);
		gd.setInsets			(0, 390, -210);
		gd.addImage				(insertImp);
		gd.addTextAreas			(aboutMessage, null, 37, 85);
		gd.setOKLabel			("Close");
		gd.hideCancelButton		();
		gd.showDialog			();

		if (gd.wasCanceled())
			return;
	}
}